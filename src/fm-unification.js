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

const freevars = ([ctor, term]) => {
    const freevars_aux = ([ctor, term], depth, vars) => {
        switch (ctor) {
        case "Var":
            return term.index < depth ? vars : vars.add(term.index - depth);
        case "Typ":
            return vars;
        case "Tid":
            return vars;
        case "All":
            return freevars_aux(term.bind, depth, vars) && freevars_aux(term.body, depth + 1, vars);
        case "Lam":
            return (!(term.bind) || freevars_aux(term.bind, depth, vars)) && freevars_aux(term.body, depth + 1, vars);
        case "App":
            return freevars_aux(term.func, depth, vars) && freevars_aux(term.argm, depth, vars);
        case "Box":
            return freevars_aux(term.expr, depth, vars);
        case "Put":
            return freevars_aux(term.expr, depth, vars);
        case "Tak":
            return freevars_aux(term.expr, depth, vars);
        case "Dup":
            return freevars_aux(term.expr, depth, vars) && freevars_aux(term.body, depth + 1, vars);
        case "Wrd":
            return vars;
        case "Num":
            return vars;
        case "Op1":
        case "Op2":
            return freevars_aux(term.num0, depth, vars) && freevars_aux(term.num1, depth, vars);
        case "Ite":
            return freevars_aux(term.cond, depth, vars) && freevars_aux(term.pair, depth, vars);
        case "Cpy":
            return freevars_aux(term.numb, depth, vars) && freevars_aux(term.body, depth + 1, vars);
        case "Sig":
            return freevars_aux(term.typ0, depth, vars) && freevars_aux(term.typ1, depth + 1, vars);
        case "Par":
            return freevars_aux(term.val0, depth, vars) && freevars_aux(term.val1, depth, vars);
        case "Fst":
            return freevars_aux(term.pair, depth, vars);
        case "Snd":
            return freevars_aux(term.pair, depth, vars);
        case "Prj":
            return freevars_aux(term.pair, depth, vars) && freevars_aux(term.body, depth + 2, vars);
        case "Eql":
            return freevars_aux(term.val0, depth, vars) && freevars_aux(term.val1, depth, vars);
        case "Rfl":
            return freevars_aux(term.expr, depth, vars);
        case "Sym":
            return freevars_aux(term.prof, depth, vars);
        case "Rwt":
            return freevars_aux(term.type, depth + 1, vars) && freevars_aux(term.prof, depth, vars) && freevars_aux(term.expr, depth, vars);
        case "Slf":
            return freevars_aux(term.type, depth + 1, vars);
        case "New":
            return freevars_aux(term.type, depth, vars) && freevars_aux(term.expr, depth, vars);
        case "Use":
            return freevars_aux(term.expr, depth, vars);
        case "Ann":
            return freevars_aux(term.type, depth, vars) && freevars_aux(term.expr, depth, vars);
        case "Log":
            return freevars_aux(term.expr, depth, vars);
        case "Hol":
            return vars;
        case "Ref":
            return vars;
        }
    }
    return freevars_aux([ctor, term], 0, new Set);
}

const is_closed = ([ctor, term]) => {
    const is_closed_aux = ([ctor, term], depth) => {
        switch (ctor) {
        case "Var":
            return term.index < depth;
        case "Typ":
            return true;
        case "Tid":
            return true;
        case "All":
            return is_closed_aux(term.bind, depth) && is_closed_aux(term.body, depth + 1);
        case "Lam":
            return (!(term.bind) || is_closed_aux(term.bind, depth)) && is_closed_aux(term.body, depth + 1);
        case "App":
            return is_closed_aux(term.func, depth) && is_closed_aux(term.argm, depth);
        case "Box":
            return is_closed_aux(term.expr, depth);
        case "Put":
            return is_closed_aux(term.expr, depth);
        case "Tak":
            return is_closed_aux(term.expr, depth);
        case "Dup":
            return is_closed_aux(term.expr, depth) && is_closed_aux(term.body, depth + 1);
        case "Wrd":
            return true;
        case "Num":
            return true;
        case "Op1":
        case "Op2":
            return is_closed_aux(term.num0, depth) && is_closed_aux(term.num1, depth);
        case "Ite":
            return is_closed_aux(term.cond, depth) && is_closed_aux(term.pair, depth);
        case "Cpy":
            return is_closed_aux(term.numb, depth) && is_closed_aux(term.body, depth + 1);
        case "Sig":
            return is_closed_aux(term.typ0, depth) && is_closed_aux(term.typ1, depth + 1);
        case "Par":
            return is_closed_aux(term.val0, depth) && is_closed_aux(term.val1, depth);
        case "Fst":
            return is_closed_aux(term.pair, depth);
        case "Snd":
            return is_closed_aux(term.pair, depth);
        case "Prj":
            return is_closed_aux(term.pair, depth) && is_closed_aux(term.body, depth + 2);
        case "Eql":
            return is_closed_aux(term.val0, depth) && is_closed_aux(term.val1, depth);
        case "Rfl":
            return is_closed_aux(term.expr, depth);
        case "Sym":
            return is_closed_aux(term.prof, depth);
        case "Rwt":
            return is_closed_aux(term.type, depth + 1) && is_closed_aux(term.prof, depth) && is_closed_aux(term.expr, depth);
        case "Slf":
            return is_closed_aux(term.type, depth + 1);
        case "New":
            return is_closed_aux(term.type, depth) && is_closed_aux(term.expr, depth);
        case "Use":
            return is_closed_aux(term.expr, depth);
        case "Ann":
            return is_closed_aux(term.type, depth) && is_closed_aux(term.expr, depth);
        case "Log":
            return is_closed_aux(term.expr, depth);
        case "Hol":
            return true;
        case "Ref":
            return false;
        }
    }
    return is_closed_aux([ctor, term], 0);
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
    var term = term;
    list.forEach((arg) => { term = App(term, arg, false); })
    return term;
}
