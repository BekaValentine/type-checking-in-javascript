/*
 *  Making representations of types
 */
var Foo = { tag: "Foo" };
var Bar = { tag: "Bar" };
var Baz = { tag: "Baz" };

function prod(a,b) {
    return { tag: "*", left: a, right: b };
}

function arr(a,b) {
    return { tag: "->", arg: a, ret: b };
}

function show(a) {
    if ("Foo" == a.tag) { return "Foo"; }
    if ("Bar" == a.tag) { return "Bar"; }
    if ("Baz" == a.tag) { return "Baz"; }
    if ("*" == a.tag) {
        return "(" + show(a.left) + "," + show(a.right) + ")";
    }
    if ("->" == a.tag) {
        return "(" + show(a.arg) + " -> " + show(a.ret) + ")";
    }
    return "Unknown";
}



/*
 *  A type
 *  ======
 */
function judgment_type(a) {
  
  /*
   *  -------- Foo Formation
   *  Foo type
   *
   *  -------- Bar Formation
   *  Bar type
   *
   *  -------- Baz Formation
   *  Baz type
   */
  if ("Foo" == a.tag || "Bar" == a.tag || "Baz" == a.tag) {
      
      return true;
      
  }
  
  /*
   *  A type    B type
   *  ---------------- * Formation
   *      A*B type
   */
  else if ("*" == a.tag) {
      
      return judgment_type(a.left) && judgment_type(a.right);
      
  }
  
  /*
   *  A type    B type
   *  ---------------- -> Formation
   *    A -> B type
   */
  else if ("->" == a.tag) {
      
      return judgment_type(a.arg) && judgment_type(a.ret);
      
  }
  
  /*
   *  Nothing else is a type.
   */
  else {
      
      return false;
      
  }
}



/*
 *  Making representations of contexts
 */
var empty = { tag: "<>" }

function snoc(g,x,a) {
    return { tag: ",:", rest: g, name: x, type: a };
}



/*
 *  Making representations of terms
 */

function pair(m,n) {
  return { tag: "(,)", first: m, second: n };
}

function split(p, x, y, m) {
    return { tag: "split",
             pair: p,
             name_x: x, name_y: y,
             body: m };
}

function lam(x,a,m) {
    return { tag: "lam", name: x, arg_type: a, body: m };
}

function app(m,n) {
    return { tag: "app", fun: m, arg: n };
}

function v(n) {
    return { tag: "variable", name: n };
}



/*
 *  Finding out what type a variable has in a context
 */
function type_lookup(g, n) {
    
    if ("<>" == g.tag) {
        
        return null;
        
    } else if (n == g.name) {
        
        return g.type
        
    } else {
        
        return type_lookup(g.rest, n);
        
    }
    
}



/*
 *  Testing if two types are equal
 */
function type_equality(a,b) {
    
    if (("Foo" == a.tag && "Foo" == b.tag) ||
        ("Bar" == a.tag && "Bar" == b.tag) ||
        ("Baz" == a.tag && "Baz" == b.tag)) {
        
        return true;
        
    } else if ("*" == a.tag && "*" == b.tag) {
        
        return type_equality(a.left, b.left) &&
               type_equality(a.right, b.right);
        
    } else if ("->" == a.tag && "->" == b.tag) {
        
        return type_equality(a.arg, b.arg) &&
               type_equality(a.ret, b.ret);
        
    } else {
        
        return false;
        
    }
    
}



/*
 *  Checking component of the judgment  G !- M : A
 */
function judgment_check(g, m, a) {
    
    /*
     *  G !- M : A    G !- N : B
     *  ------------------------ * Intro
     *      G !- (M,N) : A*B
     */
    if ("(,)" == m.tag && "*" == a.tag) {
        
        return judgment_check(g, m.first, a.left) &&
               judgment_check(g, m.second, a.right);
        
    }
    
    /*
     *  G !- P : A*B    G, x : A, y : B !- N : C
     *  ---------------------------------------- * Elim
     *       G !- split P as (x,y) in N : C
     */
    else if ("split" == m.tag) {
        
        var inferred_pair = judgment_infer(g, m);
        
        if (!inferred_pair || "*" != inferred_pair.tag) {
            return false;
        }
        
        return judgment_check(snoc(snoc(g, m.name_x, inferred_pair.left),
                                   m.name_y, inferred_pair.right),
                              m.body,
                              a);
    
    }
    
    /*
     *  G, x : A !- M : B
     *  ----------------- -> Intro
     *  G !- \x:A. M : B
     */
    else if ("lam" == m.tag && "->" == a.tag) {
        
        return type_equality(m.arg_type, a.arg) &&
               judgment_check(snoc(g, m.name, a.arg), m.body, a.ret);
        
    }
    
    /*
     *  G !- M : A -> B    G !- N : A
     *  ----------------------------- -> Elim
     *          G !- M N : B
     */
    else if ("app" == m.tag) {
        
        var inferred_arg = judgment_infer(g, m.arg);
        
        if (!inferred_arg) {
            return false;
        }
        
        return judgment_check(g, m.fun, arr(inferred_arg, a));
        
    }
    
    /*
     *  x has type A in G
     *  ----------------- variable
     *     G !- x : A
     */
    else if ("variable" == m.tag) {
        
        return type_equality(type_lookup(g, m.name), a);
        
    }
    
    /*
     *  Nothing else is well-typed
     */
    else {
        
        return false;
        
    }
    
}



/*
 *  Inference component of the judgment  G !- M : A
 */
function judgment_infer(g, m) {
    
    /*
     *  G !- M : A    G !- N : B
     *  ------------------------ * Intro
     *      G !- (M,N) : A*B
     */
    if ("(,)" == m.tag) {
        
        var inferred_left = judgment_infer(g, m.first);
        var inferred_right = judgment_infer(g, m.second);
        
        if (!inferred_left || !inferred_right) {
            return null;
        }
        
        return prod(inferred_left, inferred_right);
        
    }
    
    /*
     *  G !- P : A*B    G, x : A, y : B !- N : C
     *  ---------------------------------------- * Elim
     *       G !- split P as (x,y) in N : C
     */
    else if ("split" == m.tag) {
        
        var inferred_pair = judgment_infer(g, m.pair);
        
        if (!inferred_pair || "*" != inferred_pair.tag) {
            return null;
        }
        
        return judgment_infer(snoc(snoc(g, m.name_x, inferred_pair.left),
                                   m.name_y, inferred_pair.right),
                              m.body);
        
    }
    
    /*
     *  G, x : A !- M : B
     *  ----------------- -> Intro
     *  G !- \x:A. M : B
     */
    else if ("lam" == m.tag) {
        
        var inferred_body = judgment_infer(snoc(g, m.name, m.arg_type),
                                           m.body);
        
        if (!inferred_body) { return null; }
        
        return arr(m.arg_type, inferred_body);
        
    }
    
    /*
     *  G !- M : A -> B    G !- N : A
     *  ----------------------------- -> Elim
     *          G !- M N : B
     */
    else if ("app" == m.tag) {
        
        var inferred_fun = judgment_infer(g, m.fun);
        
        if (!inferred_fun || "->" != inferred_fun.tag ||
            !judgment_check(g, m.arg, inferred_fun.arg)) {
            
            return null;
        }
        
        return inferred_fun.ret;
        
    }
    
    /*
     *  x has type A in G
     *  ----------------- variable
     *     G !- x : A
     */
    else if ("variable" == m.tag) {
        
        return type_lookup(g, m.name);
        
    }
    
    /*
     *  Nothing else can have its type inferred
     */
    else {
        
        return null;
        
    }
    
}
