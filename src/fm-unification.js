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

const reduce = (term) => norm(term, {}, {undup: true, weak: false});

const simplify = ([t1, t2], depth) => {
    // reduce terms to weak head normal form
    t1 = norm(t1, {}, {undup: true, weak: true});
    t2 = norm(t2, {}, {undup: true, weak: true});

    const simplify_aux = ([t1, t2], depth) => {
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
                        var maybe = simplify_aux([args1[i], args2[i]], depth);
                        if (maybe === null) return null;
                        constraints.concat(maybe);
                    }
                    return constraints;
                }
                else return null;
            }
        }

        // if t1 and t2 are lambda terms, then their bodies must be equal
        if (t1[0] === "Lam" && t2[0] === "Lam"){
            return [[t1[1].body, t2[1].body]];
        }

        // if t1 and t2 are pi types, then their bodies and binds must be equal
        if (t1[0] === "All" && t2[0] === "All"){
            return [[t1[1].body, t2[1].body], [t1[1].bind, t2[1].bind]];
        }

        // in case any is stuck, we just return the same constraint, since we cannot make it any simpler
        if (is_stuck(t1) || is_stuck(t2)) {
            return [t1, t2];
        }

        // otherwise we fail
        return null;
    }

    return simplify_aux([t1, t2], depth);
}
