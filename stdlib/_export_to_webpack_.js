var arr     = require("./arr.fmc").default;
var bits    = require("./bits.fmc").default;
var bool    = require("./bool.fmc").default;
var cat     = require("./cat.fmc").default;
var fun     = require("./fun.fmc").default;
var global  = require("./global.fmc").default;
var kaelin  = require("./kaelin.fmc").default;
var keccak  = require("./keccak.fmc").default;
var list    = require("./list.fmc").default;
var maybe   = require("./maybe.fmc").default;
var main    = require("./main.fmc").default;
var nat     = require("./nat.fmc").default;
var num     = require("./num.fmc").default;
var pair    = require("./pair.fmc").default;
var pbt     = require("./pbt.fmc").default;
var stack   = require("./stack.fmc").default;
var string  = require("./string.fmc").default;
var term    = require("./term.fmc").default;
var tree    = require("./tree.fmc").default;
var tup     = require("./tup.fmc").default;
var v2      = require("./v2.fmc").default;

module.exports = [
  arr,
  bits,
  bool,
  cat,
  fun,
  global,
  kaelin,
  keccak,
  list,
  main,
  maybe,
  nat,
  num,
  pair,
  pbt,
  stack,
  string,
  term,
  tree,
  tup,
  v2,
].join("\n");
