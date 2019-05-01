#include <stdio.h>
#include <stdint.h>
#include <math.h>
#include <string>
#include <iostream>
#include <vector>
#include <algorithm>

#include <thrust/host_vector.h>
#include <thrust/device_vector.h>
#include <thrust/transform_scan.h>
#include <thrust/scan.h>

typedef  int64_t i64;
typedef uint64_t u32;
typedef uint64_t u64;
typedef double   f64;

// ::::::::::
// :: Node ::
// ::::::::::

// type=0 is a normal node
// type=1 is a duplicating node
// type=2 is a wire
__host__ __device__
u64 new_node(u64 kind, i64 a_dist, u64 a_slot, i64 b_dist, u64 b_slot, i64 c_dist, u64 c_slot) {
  return (kind << 54)
      | (a_slot << 52) | ((u64)(a_dist + 32768) << 36)
      | (b_slot << 34) | ((u64)(b_dist + 32768) << 18)
      | (c_slot << 16) | ((u64)(c_dist + 32768) <<  0);
}

__constant__
const u64 air = 0x8000600028000; // new_node(0, 0,0, 0,1, 0,2)
const u64 dot = 11259024838262784;

__host__ __device__ 
u64 to_wire(u64 node) {
  return (node & ~((u64)0x1 << 63)) | ((u64)1 << 63);
}

__host__ __device__
u64 is_wire(u64 node) {
  return (node >> 63) & 0x1;
}

__host__ __device__
u64 get_kind(u64 node) {
  return (node >> 54) & 0xFF;
}

__host__ __device__
i64 get_dist(u64 node, u64 slot) {
  return (i64)((node >> (36 - slot * 18)) & 0xFFFF) - 32768;
}

__host__ __device__
u64 get_slot(u64 node, u64 slot) {
  return ((node >> (52 - slot * 18)) & 0x3);
}

__host__ __device__
u64 inc_port(u64 node, u64 slot, i64 delta) {
  return (u64)((i64)node + (delta << (36 - slot * 18)));
}

__host__ __device__
u64 inc_ports(u64 node, i64 delta) {
  return (u64)((i64)node + (delta << 36) + (delta << 18) + delta);
}

__host__ __device__
u64 set_port(u64 node, u64 slot, i64 new_dist, u64 new_slot) {
  return (node & ~((u64)0x3FFFF << (36 - slot * 18))) | (((new_slot << 16) | (u64)(new_dist + 32768)) << (36 - slot * 18));
}

__host__ __device__
u64 has_externals(u64 node, u64 indx, u64 radius) {
  return get_dist(node, 0) + indx >= radius
      || get_dist(node, 1) + indx >= radius
      || get_dist(node, 2) + indx >= radius;
}

__host__ __device__
u64 eql(u64 a, u64 b) {
  return a == b;
}

__host__ __device__
f64 get_force(u64 node) {
  i64 x = get_dist(node, 0);
  i64 y = get_dist(node, 1);
  i64 z = get_dist(node, 2);
  return (f64)((x < 0 ? -1 : 1) * x * x + (y < 0 ? -1 : 1) * y * y + (z < 0 ? -1 : 1) * z * z);
}

__host__ __device__
u64 get_redex_type(u64 a_node, u64 b_node) {
  if (!eql(a_node, air) && !eql(b_node, air) && get_dist(a_node, 0) + get_dist(b_node, 0) == 0 && get_slot(a_node, 0) == 0) {
    return get_kind(a_node) == get_kind(b_node) ? 1 : 2;
  } else {
    return 0;
  }
}

// :::::::::
// :: Net ::
// :::::::::

struct Alloc {
  u64 indxs[4];
};

__host__ __device__
bool alloc4(u64 *net, u64 len, u64 i, u64 *indxs) {
  u64 k = 0, n, a;
  u64 j = 0;
  do {
    k = k + 1;
    n = i + ((k % 2) * 2 - 1) * (k / 2);
    a = n < len ? net[n] : 0;
    if (eql(a, air)) {
      indxs[j++] = n;
    }
  } while (k < 32 && j < 4);
  return j == 4;
}

__host__ __device__
void link(u64* net, u64 len, u64 a_indx, u64 a_slot, u64 b_indx, u64 b_slot) {
  net[a_indx] = set_port(net[a_indx], a_slot, b_indx - a_indx, b_slot);
  net[b_indx] = set_port(net[b_indx], b_slot, a_indx - b_indx, a_slot);
}

__host__ __device__
void unlink(u64 *net, u64 len, u64 a_indx, u64 a_slot) {
  u64 a_node = net[a_indx];
  u64 b_indx = get_dist(a_node, a_slot) + a_indx;
  u64 b_slot = get_slot(a_node, a_slot);
  u64 b_node = net[b_indx];
  if (get_dist(b_node, b_slot) + b_indx == a_indx && get_slot(b_node, b_slot) == a_slot) {
    net[a_indx] = set_port(a_node, a_slot, 0, a_slot);
    net[b_indx] = set_port(b_node, b_slot, 0, b_slot);
  }
}

__host__ __device__
u64 get_redex_type_at(u64* net, u64 len, u64 a_indx) {
  u64 a_node = net[a_indx];
  u64 b_indx = get_dist(a_node, 0) + a_indx;
  u64 b_node = net[b_indx];
  return get_redex_type(a_node, b_node);
};

__host__ __device__
bool rewrite(u64* net, u64 len, u64 a_indx) {
  u64 a_node = net[a_indx];
  u64 b_indx = a_indx + get_dist(a_node, 0);
  u64 b_node = net[b_indx];
  if (get_redex_type_at(net, len, a_indx) == 0) return false;
  if (get_kind(a_node) == get_kind(b_node)) {
    u64 a1_indx = get_dist(net[a_indx], 1) + a_indx;
    u64 a1_slot = get_slot(net[a_indx], 1);
    u64 b1_indx = get_dist(net[b_indx], 1) + b_indx;
    u64 b1_slot = get_slot(net[b_indx], 1);
    link(net, len, a1_indx, a1_slot, b1_indx, b1_slot);
    u64 a2_indx = get_dist(net[a_indx], 2) + a_indx;
    u64 a2_slot = get_slot(net[a_indx], 2);
    u64 b2_indx = get_dist(net[b_indx], 2) + b_indx;
    u64 b2_slot = get_slot(net[b_indx], 2);
    link(net, len, a2_indx, a2_slot, b2_indx, b2_slot);
  } else {
    u64 indxs[4] = {0, 0, 0, 0};
    if (!alloc4(net, len, (a_indx + b_indx) / 2, indxs)) return false;
    u64 c_indx = indxs[0];
    u64 d_indx = indxs[1];
    u64 e_indx = indxs[2];
    u64 f_indx = indxs[3];
    net[c_indx] = new_node(get_kind(b_node), 0,0, f_indx - c_indx, 1, e_indx - c_indx, 1); 
    net[d_indx] = new_node(get_kind(b_node), 0,0, f_indx - d_indx, 2, e_indx - d_indx, 2); 
    net[e_indx] = new_node(get_kind(a_node), 0,0, c_indx - e_indx, 2, d_indx - e_indx, 2);
    net[f_indx] = new_node(get_kind(a_node), 0,0, c_indx - f_indx, 1, d_indx - f_indx, 1);
    link(net, len, c_indx, 0, get_dist(net[a_indx],1) + a_indx, get_slot(net[a_indx],1));
    link(net, len, d_indx, 0, get_dist(net[a_indx],2) + a_indx, get_slot(net[a_indx],2));
    link(net, len, e_indx, 0, get_dist(net[b_indx],2) + b_indx, get_slot(net[b_indx],2));
    link(net, len, f_indx, 0, get_dist(net[b_indx],1) + b_indx, get_slot(net[b_indx],1));
  }
  for (int slot = 0; slot < 3; slot++) {
    unlink(net, len, a_indx, slot);
    unlink(net, len, b_indx, slot);
  }
  net[a_indx] = air;
  net[b_indx] = air;
  return true;
}

__host__ __device__
void move(u64 *net, u64 len, u64 a_indx, u64 b_indx) {
  u64 a_node = net[a_indx];
  u64 b_node = net[b_indx];
  net[b_indx] = inc_ports(a_node, -(b_indx - a_indx));
  net[a_indx] = inc_ports(b_node, -(a_indx - b_indx));
  for (u64 slot = 0; slot < 3; ++slot) {
    u64 a_dist = get_dist(a_node, slot);
    u64 a_slot = get_slot(a_node, slot);
    u64 b_dist = get_dist(b_node, slot);
    u64 b_slot = get_slot(b_node, slot);
    u64 c_indx = a_dist == 0 ? b_indx : a_dist == b_indx - a_indx ? a_indx : a_indx + a_dist;
    u64 d_indx = b_dist == 0 ? a_indx : b_dist == a_indx - b_indx ? b_indx : b_indx + b_dist;
    net[c_indx] = inc_port(net[c_indx], a_slot, b_indx - a_indx);
    net[d_indx] = inc_port(net[d_indx], b_slot, a_indx - b_indx);
  }
}

__host__ __device__
void chill(u64 *net, u64 len) {
  for (u64 i = 0; i < len - 1; i += 2) {
    if (get_force(net[i]) > get_force(net[i + 1])) {
      move(net, len, i, i + 1);
    }
  }
  for (u64 i = 1; i < len - 1; i += 2) {
    if (get_force(net[i]) > get_force(net[i + 1])) {
      move(net, len, i, i + 1);
    }
  }
}

bool is_valid(u64 *net, u64 len) {
  u64 a_indx, a_slot, a_node;
  u64 b_indx, b_slot, b_node; 
  u64 c_indx, c_slot, c_node; 
  for (a_indx = 0; a_indx < len; ++a_indx) {
    a_node = net[a_indx];
    if (!eql(a_node, air) && !is_wire(a_node)) {
      for (a_slot = 0; a_slot < 3; ++a_slot) {
        b_indx = get_dist(a_node, a_slot) + a_indx;
        b_slot = get_slot(a_node, a_slot);
        b_node = net[b_indx];
        while (is_wire(b_node)) {
          b_indx = get_dist(b_node, b_slot) + b_indx;
          b_slot = get_slot(b_node, b_slot);
          b_node = net[b_indx];
        }
        c_indx = get_dist(b_node, b_slot) + b_indx;
        c_slot = get_slot(b_node, b_slot);
        c_node = net[c_indx];
        while (is_wire(c_node)) {
          c_indx = get_dist(c_node, c_slot) + c_indx;
          c_slot = get_slot(c_node, c_slot);
          c_node = net[c_indx];
        }
        if (a_indx != c_indx || a_slot != c_slot) {
          std::cout << "bad " << a_indx << ":" << a_slot << " " << b_indx << ":" << b_slot << " " << c_indx << ":" << c_slot << std::endl;
          return false;
        }
      }
    }
  }
  return true;
}

std::vector<u64> redexes(u64 *net, u64 len) {
  std::vector<u64> redexes;
  for (u64 a_indx = 0; a_indx < len; ++a_indx) {
    u64 b_indx = get_dist(net[a_indx], 0) + a_indx;
    if (a_indx <= b_indx && get_redex_type_at(net, len, a_indx) > 0) {
      redexes.push_back(a_indx);
    }
  }
  return redexes;
}

u64 reduce_pass(u64 *net, u64 len) {
  std::vector<u64> rdx = redexes(net, len);
  u64 rwt = 0;
  for (u64 i = 0; i < rdx.size(); ++i) {
    if (rewrite(net, len, rdx[i]))  {
      rwt += 1;
    }
  }
  return rwt;
}

// ::::::::::
// :: Misc ::
// ::::::::::

std::string show_slot(u64 node, u64 slot) {
  std::string str;
  str.append(std::to_string(get_dist(node, slot)));
  switch (get_slot(node, slot)) {
    case 0: str.append("a"); break;
    case 1: str.append("b"); break;
    case 2: str.append("c"); break;
  }
  return str;
}

std::string show_node(u64 node) {
  std::string str;
  if (eql(node, air)) {
    str.append("~");
  } else {
    if (is_wire(node)) {
      str.append("-");
    } else {
      str.append(std::to_string(get_kind(node)));
    }
    for (int slot = 0; slot < 3; ++slot) {
      str.append(slot > 0 ? " " : "[");
      str.append(show_slot(node, slot));
    }
    str.append("] {");
    str.append(std::to_string(get_force(node)));
    str.append("}");
  }
  return str;
}

std::string plot_nums(std::vector<f64> &nums, std::vector<u64> &cols) {
  std::string str;
  for (uint i = 0; i < nums.size(); ++i) {
    str.append(cols[i] == 0 ? "\x1b[33m" : cols[i] == 1 ? "\x1b[32m" : cols[i] == 2 ? "\x1b[31m" : cols[i] == 3 ? "\x1b[34m" : "\x1b[35m");
    switch ((u64)(floor(fmax(fmin(nums[i],(f64)1),(f64)0) * 8))) {
      case 0: str.append(","); break;
      case 1: str.append("▁"); break;
      case 2: str.append("▂"); break;
      case 3: str.append("▃"); break;
      case 4: str.append("▄"); break;
      case 5: str.append("▅"); break;
      case 6: str.append("▆"); break;
      case 7: str.append("▇"); break;
      case 8: str.append("█"); break;
    }
    str.append("\x1b[0m");
    if (i % 256 == 255 && i < nums.size() - 1) {
      str.append("\n");
    }
  }
  return str;
};

void print_net(u64 *net, u64 len, bool show_nodes, bool show_stats, bool show_heatmap) {
  for (u64 i = 0; i < len; ++i) {
    if (show_nodes && !eql(net[i], air)) {
      std::cout << i << " - " << show_node(net[i]) << std::endl;
    }
  }
  if (show_stats) {
    std::cout << "Valid: " << is_valid(net, len) << std::endl;
  }
  if (show_heatmap) {
    std::vector<f64> nums;
    std::vector<u64> cols;
    for (u64 i = 0; i < len; ++i) {
      nums.push_back(eql(net[i], air) ? 0 : 1.0 / 8.0 + sqrt(abs(get_force(net[i]))) / 256.0);
      cols.push_back(is_wire(net[i]) ? 3 : eql(net[i],dot) ? 4 : get_redex_type_at(net, len, i));
    }
    std::cout << plot_nums(nums, cols) << std::endl;
  }
}

void print_nums(u64 *vec, u64 len) {
  for (u64 i = 0; i < len; ++i) {
    std::cout << vec[i] << " ";
  }
  std::cout << std::endl;
}

// :::::::::
// :: GPU ::
// :::::::::

/*struct is_node : public thrust::unary_function<u64,u64> {*/
  /*__host__ __device__ u64 operator()(u64 node) { return eql(node, air) ? 0 : 1; }*/
/*};*/

// Adapted from: https://www.mimuw.edu.pl/~ps209291/kgkp/slides/scan.pdf
// Note: maximum length = threads_per_block * 2
__device__ void scansum(u32 *data, u64 len) {
  u64 thid = threadIdx.x;
  u64 offset = 1;
  for (u64 d = len>>1; d > 0; d >>= 1) { // build sum in place up the tree
    __syncthreads();
    if (thid < d) {
      u64 ai = offset*(2*thid+1)-1;
      u64 bi = offset*(2*thid+2)-1;
      data[bi] += data[ai];
    }
    offset *= 2;
  }
  if (thid == 0) {
    data[len - 1] = 0;
  }
  for (u64 d = 1; d < len; d *= 2) { // traverse down tree & build scan
    offset >>= 1;
    __syncthreads();
    if (thid < d) {
      u64 ai = offset*(2*thid+1)-1;
      u64 bi = offset*(2*thid+2)-1;
      u64 t = data[ai];
      data[ai] = data[bi];
      data[bi] += t;
    }
  }
}

// Moves nodes to target locations
__device__ void move_nodes(u64 *snet, u32 *mov2) {
  u64 ti = threadIdx.x;
  u64 tmem[2];
  u64 o_indx[3];
  u64 a_indx, a_node, t_indx, t_slot, n;
  for (n = 0; n < 2; ++n) {
    a_indx = ti * 2 + n;
    tmem[n] = snet[a_indx];
  }
  __syncthreads();
  for (n = 0; n < 2; ++n) {
    a_indx = ti * 2 + n;
    snet[a_indx] = air;
  }
  __syncthreads();
  for (n = 0; n < 2; ++n) {
    a_indx = ti * 2 + n;
    a_node = tmem[n];
    t_indx = mov2[a_indx];
    if (!eql(a_node, air)) {
      for (t_slot = 0; t_slot < 3; ++t_slot) {
        o_indx[t_slot] = get_dist(a_node, t_slot) + a_indx;
        o_indx[t_slot] = o_indx[t_slot] < 2048 ? mov2[o_indx[t_slot]] : o_indx[t_slot];
      }
      snet[t_indx] = new_node(get_kind(a_node),
        (i64)o_indx[0] - (i64)t_indx, get_slot(a_node, 0),
        (i64)o_indx[1] - (i64)t_indx, get_slot(a_node, 1),
        (i64)o_indx[2] - (i64)t_indx, get_slot(a_node, 2));
    }
  }
  __syncthreads();
}

// Reduces a block of 2048 nodes on shared memory.
// `snet` is the block with the input nodes that will be reduced.
// `spos` is the global position of input nodes, which will be updated.
__device__ void reduce_block(u64 *snet, u32 *spos, u32 *smem) {
  u64 tmem[6];
  u64 a_indx, a_slot, a_node;
  u64 b_indx, b_slot, b_node;
  u64 rdx_ty, n;
  u64 ti = threadIdx.x;

  for (n = 0; n < 2; ++n) {
    smem[ti * 2 + n] = 0;
  }
  __syncthreads();
  __syncthreads();

  // Computes the dest index of each node by scan-summing their space neds.
  for (n = 0; n < 2; ++n) { 
    a_indx = ti * 2 + n;
    a_node = snet[a_indx];
    b_indx = get_dist(a_node, 0) + a_indx;
    if (b_indx < 2048) {
      b_node = snet[b_indx];
      rdx_ty = get_redex_type(a_node, b_node);
      smem[a_indx] = eql(a_node, air) ? 0 : rdx_ty == 2 ? 3 : 1;
    } else {
      smem[a_indx] = 1;
    }
  }
  scansum(smem, 2048);
  __syncthreads();

  // Checks if enough space
  if (smem[2047] > 2048) {
    return;
  }

  // Moves nodes to their target locations.
  move_nodes(snet, smem);

  // Performs annihilation and duplication reductions.
  for (n = 0; n < 2; ++n) {
    a_indx = ti * 2 + n;
    a_node = snet[a_indx];
    tmem[n * 3 + 0] = a_node;
    tmem[n * 3 + 1] = air;
    tmem[n * 3 + 2] = air;
    if (!eql(a_node, air)) {
      b_indx = get_dist(a_node, 0) + a_indx;
      if (b_indx < 2048) {
        b_node = snet[b_indx];
        if (!has_externals(a_node, a_indx, 2048) && !has_externals(b_node, b_indx, 2048)) {
          rdx_ty = get_redex_type(a_node, b_node);
          if (rdx_ty == 2) {
            tmem[n * 3 + 0] = to_wire(new_node(0, 0, 0, 1, 0, 2, 0));
            tmem[n * 3 + 1] = new_node(get_kind(b_node), get_dist(a_node, 1) - 1, get_slot(a_node, 1), (i64)(b_indx+1) - (i64)(a_indx+1), 1, (i64)(b_indx+2) - (i64)(a_indx+1), 1);
            tmem[n * 3 + 2] = new_node(get_kind(b_node), get_dist(a_node, 2) - 2, get_slot(a_node, 2), (i64)(b_indx+1) - (i64)(a_indx+2), 2, (i64)(b_indx+2) - (i64)(a_indx+2), 2);
          }
          if (rdx_ty == 1) {
            tmem[n * 3 + 0] = to_wire(new_node(0, 0, 0, (i64)b_indx - (i64)a_indx + get_dist(b_node, 1), get_slot(b_node, 1), (i64)b_indx - (i64)a_indx + get_dist(b_node, 2), get_slot(b_node, 2)));
          }
        }
      }
    }
  }
  __syncthreads();
  for (n = 0; n < 2; ++n) {
    a_indx = ti * 2 + n;
    a_node = tmem[n * 3 + 0];
    if (!eql(a_node, air)) {
      snet[a_indx + 0] = tmem[n * 3 + 0];
      if (!eql(tmem[n * 3 + 1], air)) {
        snet[a_indx + 1] = tmem[n * 3 + 1];
        snet[a_indx + 2] = tmem[n * 3 + 2];
      }
    }
  }
  __syncthreads();

  // Connects linked ports and cleans unused space.
  for (n = 0; n < 2; ++n) {
    a_indx = ti * 2 + n;
    a_node = snet[a_indx];
    if (is_wire(a_node)) {
      tmem[n] = air;
    } else {
      tmem[n] = a_node;
      if (!eql(a_node, air)) {
        for (a_slot = 0; a_slot < 3; ++a_slot) {
          b_indx = get_dist(a_node, a_slot) + a_indx;
          if (b_indx < 2048) {
            b_slot = get_slot(a_node, a_slot);
            b_node = snet[b_indx];
            while (is_wire(b_node)) {
              b_indx = get_dist(b_node, b_slot) + b_indx;
              b_slot = get_slot(b_node, b_slot);
              b_node = snet[b_indx];
            }
            tmem[n] = set_port(tmem[n], a_slot, b_indx - a_indx, b_slot);
          }
        }
      }
    }
  }
  __syncthreads();

  for (n = 0; n < 2; ++n) {
    snet[ti*2+n] = tmem[n];
    spos[ti*2+n] = blockIdx.x * blockDim.x * 2 + smem[spos[ti*2+n] - blockIdx.x * blockDim.x * 2];
  }
  __syncthreads();
}

// Moves nodes around in order to minimize their summed distances
__device__ void chill_block(u64 *snet, u32 *spos, u32 *smem) {
  u64 tmem[2];
  u64 a_indx, b_indx, n;
  u64 ti = threadIdx.x;
  
  // Starts smem; initially, it maps target index to source index
  for (u64 n = 0; n < 2; ++n) {
    smem[ti * 2 + n] = ti * 2 + n;
  }
  __syncthreads();

  // Performs movements
  for (u64 k = 0; k < 8; ++k) {
    u64 p = k & 1;
    if (p == 0 || ti > 0) {
      a_indx = smem[ti * 2 + 0 - p];
      b_indx = smem[ti * 2 + 1 - p];
      if (get_force(snet[a_indx]) > get_force(snet[b_indx])) {
        smem[ti * 2 + 0 - p] = b_indx;
        smem[ti * 2 + 1 - p] = a_indx;
      }
    }
    __syncthreads();
  }

  /*a_indx = smem[ti * 2 + 0];*/
  /*b_indx = smem[ti * 2 + 1];*/
  /*smem[ti * 2 + 0] = b_indx;*/
  /*smem[ti * 2 + 1] = a_indx;*/
  /*__syncthreads();*/

  // Inverses smem, so that it maps source index to target index
  // smem = 7 3 1 0 2 5 4 6 (initially)
  // smem = 3 2 4 1 6 5 7 0 (inversed)
  for (u64 n = 0; n < 2; ++n) {
    tmem[n] = smem[ti * 2 + n];
  }
  __syncthreads();
  for (u64 n = 0; n < 2; ++n) {
    smem[tmem[n]] = ti * 2 + n;
  }
  __syncthreads();

  // Moves modes to their target locations.
  move_nodes(snet, smem);
  __syncthreads();

  // Saves data
  for (n = 0; n < 2; ++n) {
    spos[ti*2+n] = blockIdx.x * blockDim.x * 2 + smem[spos[ti*2+n] - blockIdx.x * blockDim.x * 2];
  }
  __syncthreads();
}

// Reduces all blocks in parallel.
__global__ void reduce_blocks(u64 *gnet, u64 *gpos, u64 local_passes) {
  __shared__ u64 snet[2048];
  __shared__ u32 spos[2048];
  __shared__ u32 smem[2048];

  u64 ti = threadIdx.x;
  u64 gi = blockIdx.x * blockDim.x + ti;

  // Loads a block of 2048 nodes (16kb) from global memory.
  for (u64 n = 0; n < 2; ++n) {
    snet[ti*2+n] = gnet[gi*2+n];
    spos[ti*2+n] = gpos[gi*2+n];
  }
  __syncthreads();

  // Performs a few parallel reductions.
  for (u64 pass = 0; pass < local_passes; ++pass) {
    reduce_block(snet, spos, smem);
  }
  for (u64 pass = 0; pass < local_passes * 8; ++pass) {
    chill_block(snet, spos, smem);
  }
  __syncthreads();

  // Writes results back to global memory.
  for (u64 n = 0; n < 2; ++n) {
    gnet[gi*2+n] = snet[ti*2+n];
    gpos[gi*2+n] = spos[ti*2+n];
  }
}

// Reconnects cross-block links.
__global__ void adjust_cross_block_links(u64 *gnet, u64 *gpos) {
  u64 gi = blockIdx.x * blockDim.x + threadIdx.x;
  for (u64 n = 0; n < 2; ++n) {
    u64 a_indx = gi*2+n;
    u64 a_node = gnet[a_indx];
    if (!eql(a_node, air)) {
      for (u64 a_slot = 0; a_slot < 3; ++a_slot) {
        u64 i_indx = gi * 2 - (gi * 2 % 2048);
        u64 b_indx = get_dist(a_node, a_slot) + a_indx;
        u64 b_slot = get_slot(a_node, a_slot);
        if (b_indx < i_indx || b_indx >= i_indx + 2048) {
          a_node = set_port(a_node, a_slot, gpos[b_indx] - a_indx, b_slot);
        }
      }
      gnet[gi*2+n] = a_node;
    }
  }
}

// Compacts net, removing gaps and expanding as needed
__global__ void compact(u64 *src, u64 *dst, u64 *gloc, u64 expand) {
  u64 src_indx = blockIdx.x * blockDim.x + threadIdx.x;
  u64 dst_indx = (src_indx + gloc[src_indx / 2048] - (src_indx / 2048 * 2048)) * expand;
  u64 node = src[src_indx]; 
  if (!eql(node, air)) {
    u64 x_src_indx = get_dist(node, 0) + src_indx;
    u64 x_dst_indx = (x_src_indx + gloc[x_src_indx / 2048] - (x_src_indx / 2048 * 2048)) * expand;
    u64 y_src_indx = get_dist(node, 1) + src_indx;
    u64 y_dst_indx = (y_src_indx + gloc[y_src_indx / 2048] - (y_src_indx / 2048 * 2048)) * expand;
    u64 z_src_indx = get_dist(node, 2) + src_indx;
    u64 z_dst_indx = (z_src_indx + gloc[z_src_indx / 2048] - (z_src_indx / 2048 * 2048)) * expand;
    dst[dst_indx] = new_node(get_kind(node),
      (i64)x_dst_indx - (i64)dst_indx, get_slot(node, 0),
      (i64)y_dst_indx - (i64)dst_indx, get_slot(node, 1),
      (i64)z_dst_indx - (i64)dst_indx, get_slot(node, 2));
  }
}


// Gets number of nodes in each block
__global__ void get_block_max_index(u64 *gnet, u64 *gmax) {
  __shared__ u32 smem[2048];

  u64 ti = threadIdx.x;
  u64 gi = blockIdx.x * blockDim.x + threadIdx.x;

  for (u64 n = 0; n < 2; ++n) {
    smem[ti*2+n] = eql(gnet[gi*2+n],air) ? 0 : ti*2+n;
  }
  __syncthreads();

  for (u64 l = 0; l <= 10; ++l) {
    if (ti < (1024 >> l)) {
      u64 i = ti * (2 << l);
      u64 j = i + (2 << l >> 1);
      smem[i] = max(smem[i], smem[j]);
    }
    __syncthreads();
  }

  if (ti == 0) {
    gmax[gi] = smem[0] + 1;
  }
  __syncthreads();
}

std::vector<u64> parallel_reduce(u64 *net, u64 len) {
  const u64 global_passes = 36;
  const u64 local_passes = 16;

  const u64 max_nodes = 2048 * 2;
  const u64 nodes_per_block = 2048;
  const u64 total_blocks = max_nodes / nodes_per_block;
  const u64 threads_per_block = 1024;

  // Allocates memory on the CPU
  thrust::host_vector<u64> h_net(max_nodes);
  thrust::host_vector<u64> h_pos(max_nodes);
  thrust::host_vector<u64> h_loc(total_blocks);

  // Allocates memory on the GPU
  thrust::device_vector<u64> d_net(max_nodes);
  thrust::device_vector<u64> d_tmp(max_nodes);
  thrust::device_vector<u64> d_pos(max_nodes);
  thrust::device_vector<u64> d_loc(total_blocks);

  // Builds data on the CPU
  thrust::fill(h_net.begin(), h_net.begin() + h_net.size(), air);
  for (int i = 0; i < len; ++i) {
    h_net[i] = net[i];
  }

  // Sends data to the GPU
  d_net = h_net;
  d_pos = h_pos;

  for (u64 pass = 0; pass < global_passes; ++pass) {
    // Cleans position buffer
    thrust::sequence(d_pos.begin(), d_pos.end());

    // Reduces each block in isolation
    reduce_blocks<<<max_nodes / nodes_per_block, threads_per_block>>>(
      thrust::raw_pointer_cast(&d_net[0]),
      thrust::raw_pointer_cast(&d_pos[0]),
      local_passes);

    // Adjust cross-blocks links
    adjust_cross_block_links<<<max_nodes / nodes_per_block, threads_per_block>>>(
      thrust::raw_pointer_cast(&d_net[0]),
      thrust::raw_pointer_cast(&d_pos[0]));

    // Gets the new location of each block
    get_block_max_index<<<max_nodes / nodes_per_block, threads_per_block>>>(
      thrust::raw_pointer_cast(&d_net[0]),
      thrust::raw_pointer_cast(&d_loc[0]));
    thrust::exclusive_scan(d_loc.begin(), d_loc.end(), d_loc.begin());

    // Compacts net
    thrust::fill(d_tmp.begin(), d_tmp.end(), air);
    compact<<<max_nodes / 256, 256>>>(
      thrust::raw_pointer_cast(&d_net[0]),
      thrust::raw_pointer_cast(&d_tmp[0]),
      thrust::raw_pointer_cast(&d_loc[0]),
      1);
    d_net = d_tmp;

    // DEBUG: Sends to CPU & prints
    h_net = d_net;
    std::cout << "After pass " << pass << ":" << std::endl;
    print_net(&h_net[0], h_net.size(), false, true, true);
  }

  // Sends data to the CPU
  h_net = d_net;
  h_loc = d_loc;

  // Builds result vector
  std::vector<u64> result;
  for (int i = 0; i < max_nodes; ++i) {
    result.push_back(h_net[i]);
  }

  return result;
}

// ::::::::::
// :: Main ::
// ::::::::::

struct is_node : public thrust::unary_function<u64,u64> {
  __host__ __device__ u64 operator()(u64 node) { return eql(node, air) ? 0 : 1; }
};

/*std::vector<u64> net = {0x0028000a00f08000,0x0028001200b8803b,0x0028001a006c7fff,0x0008001a00207fff,0x0007fff200108001,0x0027fff200088001,0x0027fff600048003,0x0017ffe5fffd8001,0x0017ffc9fffc8002,0x0027ffd600068001,0x0027ffe5fffe7fff,0x0008001a00217ff8,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0008001200217ff8,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0017ff8600008001,0x0027fffa00018000,0x0008001a00217fe5,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0008001200217ff8,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0017ff8600008001,0x0027fffa00018000,0x0017fd26000e8001,0x00280012002a7fff,0x00280012001c7fff,0x00080015fff47fff,0x0007fff200108001,0x0027fff6000c8001,0x0027fff600068001,0x00280015fffe7fff,0x0017ffc5fff47fff,0x0017ff9600008001,0x0027fffa00018000,0x0017ff6a00048001,0x0027fff600017fff,0x0027fc5200057fc4,0x0017fffa00048001,0x0027fff600017fff};*/
std::vector<u64> net = {0x0028000a03788000,0x00280012034080dd,0x0028001a02f47fff,0x0008001a00207fff,0x0007fff200108001,0x0027fff200088001,0x0027fff600048003,0x0017ffe5fffd8001,0x0017ffc9fffc8002,0x0027ffd600068001,0x0027ffe5fffe7fff,0x0028001a02897ff8,0x0008001a00207fff,0x0007fff200108001,0x0027fff200088001,0x0027fff600048003,0x0017ffe5fffd8001,0x0017ffc9fffc8002,0x0027ffd600068001,0x0027ffe5fffe7fff,0x0028001a021d7ff8,0x0008001a00207fff,0x0007fff200108001,0x0027fff200088001,0x0027fff600048003,0x0017ffe5fffd8001,0x0017ffc9fffc8002,0x0027ffd600068001,0x0027ffe5fffe7fff,0x0028001a01b17ff8,0x0008001a00207fff,0x0007fff200108001,0x0027fff200088001,0x0027fff600048003,0x0017ffe5fffd8001,0x0017ffc9fffc8002,0x0027ffd600068001,0x0027ffe5fffe7fff,0x0028001a01457ff8,0x0008001a00207fff,0x0007fff200108001,0x0027fff200088001,0x0027fff600048003,0x0017ffe5fffd8001,0x0017ffc9fffc8002,0x0027ffd600068001,0x0027ffe5fffe7fff,0x0028001a00d97ff8,0x0008001a00207fff,0x0007fff200108001,0x0027fff200088001,0x0027fff600048003,0x0017ffe5fffd8001,0x0017ffc9fffc8002,0x0027ffd600068001,0x0027ffe5fffe7fff,0x0028001a006d7ff8,0x0008001a00207fff,0x0007fff200108001,0x0027fff200088001,0x0027fff600048003,0x0017ffe5fffd8001,0x0017ffc9fffc8002,0x0027ffd600068001,0x0027ffe5fffe7fff,0x0008001a00217ff8,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0008001200217ff8,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0017ff8600008001,0x0027fffa00018000,0x0008001a00217fe5,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0008001200217ff8,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0017ff8600008001,0x0027fffa00018000,0x0008001a00217fca,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0008001200217ff8,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0017ff8600008001,0x0027fffa00018000,0x0008001a00217faf,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0008001200217ff8,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0017ff8600008001,0x0027fffa00018000,0x0008001a00217f94,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0008001200217ff8,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0017ff8600008001,0x0027fffa00018000,0x0008001a00217f79,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0008001200217ff8,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0017ff8600008001,0x0027fffa00018000,0x0008001a00217f5e,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0008001200217ff8,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0017ff8600008001,0x0027fffa00018000,0x0008001a00217f43,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0008001200217ff8,0x0007fff200088001,0x0027fff200108002,0x0017ffe6000c8004,0x0027ffe6000e8001,0x0028001a000a7fff,0x0057ffc5fff47fff,0x0027ffc5fff57ffe,0x0017ff8600008001,0x0027fffa00018000,0x0017f306000e8001,0x00280012002a7fff,0x00280012001c7fff,0x00080015fff47fff,0x0007fff200108001,0x0027fff6000c8001,0x0027fff600068001,0x00280015fffe7fff,0x0017ffc5fff47fff,0x0017ff9600008001,0x0027fffa00018000,0x0017ff6a00048001,0x0027fff600017fff,0x0027f23200057f22,0x0017fffa00048001,0x0027fff600017fff};

int main(void) {
  /*std::cout << (u64)((u64)10 + ((i64)(-4))) << std::endl;*/

  // Prints it
  std::cout << "Input net: " << std::endl;
  print_net(&net[0], net.size(), false, true, true);

  // Reduces
  std::vector<u64> net2 = parallel_reduce(&net[0], net.size());

  // Sends to CPU & prints
  /*print_net(&net2[0], net2.size(), false, true, true);*/

  return 0;
}


// TODO: when  
