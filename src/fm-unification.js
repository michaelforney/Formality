const {
  Var,
  Typ,
  Tid,
  All,
  Lam,
  App,
  Box,
  Put,
  Tak,
  Dup,
  Wrd,
  Num,
  Op1,
  Op2,
  Ite,
  Cpy,
  Sig,
  Par,
  Fst,
  Snd,
  Prj,
  Eql,
  Rfl,
  Sym,
  Rwt,
  Slf,
  New,
  Use,
  Ann,
  Log,
  Hol,
  Ref,
  get_float_on_word,
  put_float_on_word,
  show,
  shift,
  subst,
  subst_many,
  norm,
  erase,
  equal,
  uses,
  boxcheck,
  typecheck,
  ctx_new,
  ctx_ext,
  ctx_get,
  ctx_str,
  ctx_names,
} = require("./fm-core.js");

const metavars = ([ctor, term]) => {
    const metavars_aux = ([ctor, term], vars) => {
        switch (ctor) {
        case "Var":
            return vars;
        case "Typ":
            return vars;
        case "Tid":
            return vars;
        case "All":
            return metavars_aux(term.bind, vars) && metavars_aux(term.body, vars);
        case "Lam":
            return (!(term.bind) || metavars_aux(term.bind, vars)) && metavars_aux(term.body, vars);
        case "App":
            return metavars_aux(term.func, vars) && metavars_aux(term.argm, vars);
        case "Box":
            return metavars_aux(term.expr, vars);
        case "Put":
            return metavars_aux(term.expr, vars);
        case "Tak":
            return metavars_aux(term.expr, vars);
        case "Dup":
            return metavars_aux(term.expr, vars) && metavars_aux(term.body, vars);
        case "Wrd":
            return vars;
        case "Num":
            return vars;
        case "Op1":
        case "Op2":
            return metavars_aux(term.num0, vars) && metavars_aux(term.num1, vars);
        case "Ite":
            return metavars_aux(term.cond, vars) && metavars_aux(term.pair, vars);
        case "Cpy":
            return metavars_aux(term.numb, vars) && metavars_aux(term.body, vars);
        case "Sig":
            return metavars_aux(term.typ0, vars) && metavars_aux(term.typ1, vars);
        case "Par":
            return metavars_aux(term.val0, vars) && metavars_aux(term.val1, vars);
        case "Fst":
            return metavars_aux(term.pair, vars);
        case "Snd":
            return metavars_aux(term.pair, vars);
        case "Prj":
            return metavars_aux(term.pair, vars) && metavars_aux(term.body, vars);
        case "Eql":
            return metavars_aux(term.val0, vars) && metavars_aux(term.val1, vars);
        case "Rfl":
            return metavars_aux(term.expr, vars);
        case "Sym":
            return metavars_aux(term.prof, vars);
        case "Rwt":
            return metavars_aux(term.type, vars) && metavars_aux(term.prof, vars) && metavars_aux(term.expr, vars);
        case "Slf":
            return metavars_aux(term.type, vars);
        case "New":
            return metavars_aux(term.type, vars) && metavars_aux(term.expr, vars);
        case "Use":
            return metavars_aux(term.expr, vars);
        case "Ann":
            return metavars_aux(term.type, vars) && metavars_aux(term.expr, vars);
        case "Log":
            return metavars_aux(term.expr, vars);
        case "Hol":
            return vars.add(term.name);
        case "Ref":
            return vars;
        }
    }
    return metavars_aux([ctor, term], new Set);
}

const is_closed = ([ctor, term], depth) => {
    switch (ctor) {
    case "Var":
        return term.index < depth;
    case "Typ":
        return true;
    case "Tid":
        return true;
    case "All":
        return is_closed(term.bind, depth) && is_closed(term.body, depth + 1);
    case "Lam":
        return (!(term.bind) || is_closed(term.bind, depth)) && is_closed(term.body, depth + 1);
    case "App":
        return is_closed(term.func, depth) && is_closed(term.argm, depth);
    case "Box":
        return is_closed(term.expr, depth);
    case "Put":
        return is_closed(term.expr, depth);
    case "Tak":
        return is_closed(term.expr, depth);
    case "Dup":
        return is_closed(term.expr, depth) && is_closed(term.body, depth + 1);
    case "Wrd":
        return true;
    case "Num":
        return true;
    case "Op1":
    case "Op2":
        return is_closed(term.num0, depth) && is_closed(term.num1, depth);
    case "Ite":
        return is_closed(term.cond, depth) && is_closed(term.pair, depth);
    case "Cpy":
        return is_closed(term.numb, depth) && is_closed(term.body, depth + 1);
    case "Sig":
        return is_closed(term.typ0, depth) && is_closed(term.typ1, depth + 1);
    case "Par":
        return is_closed(term.val0, depth) && is_closed(term.val1, depth);
    case "Fst":
        return is_closed(term.pair, depth);
    case "Snd":
        return is_closed(term.pair, depth);
    case "Prj":
        return is_closed(term.pair, depth) && is_closed(term.body, depth + 2);
    case "Eql":
        return is_closed(term.val0, depth) && is_closed(term.val1, depth);
    case "Rfl":
        return is_closed(term.expr, depth);
    case "Sym":
        return is_closed(term.prof, depth);
    case "Rwt":
        return is_closed(term.type, depth + 1) && is_closed(term.prof, depth) && is_closed(term.expr, depth);
    case "Slf":
        return is_closed(term.type, depth + 1);
    case "New":
        return is_closed(term.type, depth) && is_closed(term.expr, depth);
    case "Use":
        return is_closed(term.expr, depth);
    case "Ann":
        return is_closed(term.type, depth) && is_closed(term.expr, depth);
    case "Log":
        return is_closed(term.expr, depth);
    case "Hol":
        return true;
    case "Ref":
        return false;
    }
}

const is_stuck = ([ctor, term]) => {
    if (ctor === "Hol") {
        return true;
    }
    else if (ctor === "App") {
        return is_stuck(term.func);
    }
    else {
        return false;
    }
}

const peel_ap_telescope = ([ctor, args]) => {
    var term = [ctor, args];
    var list = [];
    if (term[0] === "App"){
        var argm = term[1].argm;
        [term, list] = peel_ap_telescope(term[1].func);
        list.push(argm);
    }
    return [term, list];
}

const apply_ap_telescope = ([term, list]) => {
    list.forEach((arg) => { term = App(term, arg, false); })
    return term;
}

const simplify = ([t1, t2, depth]) => {
    // reduce terms to weak head normal form
    t1 = norm(t1, {}, {undup: true, weak: true});
    t2 = norm(t2, {}, {undup: true, weak: true});
    // if t1 and t2 are equal, we are done
    if (equal(t1, t2, {})){
        return [];
    }

    // if t1 and t2 are terms of form A(a1, ..., an) and B(b1, ..., bm) where A and B are free variables, then n = m and A = B; otherwise we fail. We then unify all ai and bi.
    var [func1, args1] = peel_ap_telescope(t1);
    if (func1[0] === "Var" && func1[1].index >= depth){
        var [func2, args2] = peel_ap_telescope(t2);
        if (func2[0] === "Var" && func2[1].index >= depth){
            if(func1[1].index === func2[1].index && args1.length === args2.length){
                var constraints = [];
                for (var i = 0; i < args1.index; ++i) {
                    var maybe = simplify_aux([args1[i], args2[i], depth]);
                    if (!maybe) return null;
                    constraints.concat(maybe);
                }
                return constraints;
            }
            else return null;
        }
    }

    // if t1 and t2 are lambda terms, then their bodies must be equal
    if (t1[0] === "Lam" && t2[0] === "Lam"){
        return [[t1[1].body, t2[1].body, depth+1]];
    }

    // if t1 and t2 are pi types, then their bodies and binds must be equal
    if (t1[0] === "All" && t2[0] === "All"){
        return [[t1[1].body, t2[1].body, depth+1], [t1[1].bind, t2[1].bind, depth]];
    }

    // in case any is stuck, we just return the same constraint, since we cannot make it any simpler
    if (is_stuck(t1) || is_stuck(t2)) {
        return [[t1, t2, depth]];
    }

    // otherwise we fail
    return null;
}

// Streams constructors
const nils = () => []
const conss = (x, xs) => {
    var memo = null;
    return () => memo||(memo=[x, xs]);
}

// Stream functions
const is_empty = (xs) => {
    return xs().length === 0;
}

const head = (xs) => {
    return xs()[0];
}

const tail = (xs) => {
    return xs()[1];
}

const build_stream = (func) => (function go(n) {
    var memo = null;
    return () => memo||(memo=[func(n), go(n + 1)]);
})(0)

// Generate substitutions
const try_flex_rigid = ([t1, t2, depth]) => {
    var [func1, args1] = peel_ap_telescope(t1);
    var [func2, args2] = peel_ap_telescope(t2);
    if (func1[0] === "Hol" && !metavars(t2).has(func1[1].name)){
        return generate_subst(args1.length, func1[1].name, func2, depth);
    }
    if (func2[0] === "Hol" && !metavars(t1).has(func2[1].name)){
        return generate_subst(args2.length, func2[1].name, func1, depth);
    }
    return nils;
}

const generate_subst = (bvars, mv, f, depth) => {
    return build_stream((nargs) => {
        const mk_lam = (term) => {
            for (var i = 0; i < bvars; ++i) {
                term = Lam("a"+i, false, term, false);
            }
            return term;
        }

        const saturate_MV = (term) => {
            for (var i = 0; i < bvars; ++i) {
                term = App(term, Var(i));
            }
            return term;
        }

        const build_term = (term) => {
            for (var i = 0; i < nargs; ++i){
                term = App(term, saturate_MV(Hol(i+mv)));
            }
            return mk_lam(term);
        }

        var substs = [];
        for (var i = 0; i < bvars; ++i){
            var subst = {};
            subst[mv] = build_term(Var(i));
            substs.push(subst);
        }
        if (is_closed(f, depth)){
            var subst = {};
            subst[mv] = build_term(f);
            substs.push(subst);
        }
        return substs;
    })
}

const subst_mv = (val, mv, [ctor, term]) => {
    switch (ctor) {
    case "All":
      var name = term.name;
      var bind = subst_mv(val, mv, term.bind);
      var body = subst_mv(val, mv, term.body);
      var eras = term.eras;
      return All(name, bind, body, eras);
    case "Lam":
      var name = term.name;
      var bind = term.bind && subst_mv(val, mv, term.bind);
      var body = subst_mv(val, mv, term.body);
      var eras = term.eras;
      return Lam(name, bind, body, eras);
    case "App":
      var func = subst_mv(val, mv, term.func);
      var argm = subst_mv(val, mv, term.argm);
      var eras = term.eras;
      return App(func, argm, eras);
    case "Box":
      var expr = subst_mv(val, mv, term.expr);
      return Box(expr);
    case "Put":
      var expr = subst_mv(val, mv, term.expr);
      return Put(expr);
    case "Tak":
      var expr = subst_mv(val, mv, term.expr);
      return Tak(expr);
    case "Dup":
      var name = term.name;
      var expr = subst_mv(val, mv, term.expr);
      var body = subst_mv(val, mv, term.body);
      return Dup(name, expr, body);
    case "Op1":
    case "Op2":
      var func = term.func;
      var num0 = subst_mv(val, mv, term.num0);
      var num1 = subst_mv(val, mv, term.num1);
      return Op2(func, num0, num1);
    case "Ite":
      var cond = subst_mv(val, mv, term.cond);
      var pair = subst_mv(val, mv, term.pair);
      return Ite(cond, pair);
    case "Cpy":
      var name = term.name;
      var numb = subst_mv(val, mv, term.numb);
      var body = subst_mv(val, mv, term.body);
      return Cpy(name, numb, body);
    case "Sig":
      var name = term.name;
      var typ0 = subst_mv(val, mv, term.typ0);
      var typ1 = subst_mv(val, mv, term.typ1);
      var eras = term.eras;
      return Sig(name, typ0, typ1, eras);
    case "Par":
      var val0 = subst_mv(val, mv, term.val0);
      var val1 = subst_mv(val, mv, term.val1);
      var eras = term.eras;
      return Par(val0, val1, eras);
    case "Fst":
      var pair = subst_mv(val, mv, term.pair);
      var eras = term.eras;
      return Fst(pair, eras);
    case "Snd":
      var pair = subst_mv(val, mv, term.pair);
      var eras = term.eras;
      return Snd(pair, eras);
    case "Prj":
      var nam0 = term.nam0;
      var nam1 = term.nam1;
      var pair = subst_mv(val, mv, term.pair);
      var body = subst_mv(val, mv, term.body);
      var eras = term.eras;
      return Prj(nam0, nam1, pair, body, eras);
    case "Eql":
      var val0 = subst_mv(val, mv, term.val0);
      var val1 = subst_mv(val, mv, term.val1);
      return Eql(val0, val1);
    case "Rfl":
      var expr = subst_mv(val, mv, term.expr);
      return Rfl(expr);
    case "Sym":
      var prof = subst_mv(val, mv, term.prof);
      return Sym(prof);
    case "Rwt":
      var name = term.name;
      var type = subst_mv(val, mv, term.type);
      var prof = subst_mv(val, mv, term.prof);
      var expr = subst_mv(val, mv, term.expr);
      return Rwt(name, type, prof, expr);
    case "Slf":
      var name = term.name;
      var type = subst_mv(val, mv, term.type);
      return Slf(name, type);
    case "New":
      var type = subst_mv(val, mv, term.type);
      var expr = subst_mv(val, mv, term.expr);
      return New(type, expr);
    case "Use":
      var expr = subst_mv(val, mv, term.expr);
      return Use(expr);
    case "Ann":
      var type = subst_mv(val, mv, term.type);
      var expr = subst_mv(val, mv, term.expr);
      var done = term.done;
      return Ann(type, expr, done);
    case "Log":
      var msge = subst_mv(val, mv, term.msge);
      var expr = subst_mv(val, mv, term.expr);
      return Log(msge, expr);
    case "Hol":
        return (term.name === mv ? val : [ctor, term]);
    case "Ref":
        return [ctor, term];
    }
    return [ctor, term];
}

const many_subst = (subst, term) => {
    for (var [key, val] of Object.entries(subst)) {
        term = subst_mv(val, key, term);
    }
    return term;
}

const disj_merge = (subst1, subst2) => {
    var union = {};
    for (var [key, val] of Object.entries(subst1)) {
        union[key] = val;
    }
    for (var [key, val] of Object.entries(subst2)) {
        if (union.hasOwnProperty(key)) return null;
        union[key] = many_subst(subst1, val);
    }
    return union;
}

const equal_constraints = (cnst1, cnst2) => {
    return equal(cnst1[0], cnst2[0], {}) && equal(cnst1[1], cnst2[1], {}) && cnst1[2] === cnst2[2]
}

const repeated_simplify = (constraints) => {
    var new_constraints = [];
    var is_equal = true;
    for (var x of constraints) {
        var simpl_constraints = simplify(x);
        if (!simpl_constraints) {
            return null;
        }
        if ((simpl_constraints.length !== 1) || !equal_constraints(simpl_constraints[0], x)){
            is_equal = false;
        }
        for (var y of simpl_constraints) {
            new_constraints.push(y);
        }
    }
    if (is_equal){
        return new_constraints;
    }
    return repeated_simplify(new_constraints);
}

const apply_subst = (s, cnsts) => {
    var new_cnsts = [];
    for (var [t1, t2, depth] of cnsts) {
        new_cnsts.push([many_subst(s, t1), many_subst(s, t2), depth]);
    }
    return new_cnsts;
}

const flexflex = (t1, t2) => {
    return is_stuck(t1) && is_stuck(t2);
}

const get = (n, list) => {
  for (var i = 0; i < n; ++i) {
    list = list()[1];
  }
  return list()[0];
};

const take = (n, xs) => {
    var ys = [];
    for (var i = 0; i < n; ++i) {
        ys.push(get(i, xs));
    }
    return ys;
}

// Unify
const unify = (subst, cnsts) => {
    var new_cnsts = repeated_simplify(apply_subst(subst, cnsts));
    if (!new_cnsts) {
        return null;
    }

    var flexflexes = [];
    var flexrigids = [];
    for (var cnst of new_cnsts) {
        if (flexflex(cnst)) {
            flexflexes.push(cnst);
        }
        else {
            flexrigids.push(cnst);
        }
    }
    if (flexrigids.length === 0) {
        return [subst, flexflexes];
    }
    var random_eq = Math.floor(Math.random()*flexrigids.length);
    var psubsts = try_flex_rigid(flexrigids[random_eq]);

    const try_substs = (psubsts, cnsts) => {
        if (is_empty(psubsts)) {
            return null;
        }
        let ret = null;
        for (var new_subst of head(psubsts)) {
            ret = unify(disj_merge(new_subst, subst), cnsts);
            if (ret) return ret;
        }
        return try_substs(tail(psubsts), cnsts);
    }

    return try_substs(psubsts, flexrigids.concat(flexflexes));
}

const driver = (cnst) => unify({}, [cnst]);
