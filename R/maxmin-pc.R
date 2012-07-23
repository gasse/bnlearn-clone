
maxmin.pc.optimized = function(x, whitelist, blacklist, test,
  alpha, B, strict, debug = FALSE) {

  nodes = names(x)
  mb = list()

  for (node in nodes) {

    backtracking = unlist(sapply(mb, function(x){ node %in% x$nbr }))

    # use only the known bad nodes for backtracking, to allow
    # MMPC's AND filter on neighbourhoods
    if (!is.null(backtracking)) {
      backtracking = backtracking[!backtracking]
      if (length(backtracking) == 0)
        backtracking = NULL
    }#THEN
    
    # 1. [Forward Phase (I)]
    pcs = maxmin.pc.forward.phase(x = node, data = x, nodes = nodes,
          alpha = alpha, B = B, whitelist = whitelist, blacklist = blacklist,
          backtracking = backtracking, test = test, debug = debug)
    
    # 2. [Backward Phase (II)]
    pc = maxmin.pc.backward.phase(t = node, pcs = pcs, data = x, nodes = nodes,
          alpha = alpha, B = B, whitelist = whitelist, blacklist = blacklist,
          backtracking = backtracking, test = test, debug = debug)
    
    mb[[node]] = list(mb = pcs, nbr = pc)

  }#FOR

  # check neighbourhood sets for consistency.
  mb = bn.recovery(mb, nodes = nodes, strict = strict, debug = debug)

  return(mb)

}#MAXMIN.PC.OPTIMIZED

maxmin.pc.cluster = function(x, cluster, whitelist, blacklist,
  test, alpha, B, strict, debug = FALSE) {

  nodes = names(x)

  # 1. [Forward Phase (I)]
  pcs = parLapply(cluster, as.list(nodes), maxmin.pc.forward.phase, data = x,
         nodes = nodes, alpha = alpha, B = B, whitelist = whitelist,
         blacklist = blacklist, test = test, debug = debug)
  names(pcs) = nodes

  # 2. [Backward Phase (II)]
  apply.fun = function(x, data, nodes, alpha, B, whitelist, blacklist,
                          test, debug) {
    maxmin.pc.backward.phase(
      t=x$node, pcs=x$pcs, data = data, nodes = nodes,
      alpha = alpha, B = B, whitelist = whitelist,
      blacklist = blacklist, test = test, debug = debug)
  }
  
  apply.params = lapply(nodes, function(x) {list(node = x, pcs = pcs[[x]])})
  
  pc = parLapply(cluster, apply.params, apply.fun,
                 data = x, nodes = nodes, alpha = alpha, B = B,
                 whitelist = whitelist, blacklist = blacklist, test = test,
                 debug = debug)
  names(pc) = nodes
  
  mb = lapply(nodes, function(x) {list(mb=pcs[[x]], nbr=pc[[x]])})
  names(mb) = nodes

  # check neighbourhood sets for consistency.
  mb = bn.recovery(mb, nodes = nodes, strict = strict, debug = debug)

  return(mb)

}#MAXMIN.PC.CLUSTER

maxmin.pc = function(x, whitelist, blacklist, test, alpha, B,
  strict, debug = FALSE) {

  nodes = names(x)

  # 1. [Forward Phase (I)]
  pcs = lapply(as.list(nodes), maxmin.pc.forward.phase, data = x,
     nodes = nodes, alpha = alpha, B = B, whitelist = whitelist,
     blacklist = blacklist, test = test, backtracking = NULL, debug = debug)
  names(pcs) = nodes

  # 2. [Backward Phase (II)]
  apply.fun = function(x, data, nodes, alpha, B, whitelist, blacklist,
                        test, debug) {
    maxmin.pc.backward.phase(
      t=x$node, pcs=x$pcs, data = data, nodes = nodes,
      alpha = alpha, B = B, whitelist = whitelist,
      blacklist = blacklist, test = test, debug = debug)
  }
  
  apply.params = lapply(nodes, function(x) {list(node = x, pcs = pcs[[x]])})
  
  pc = lapply(apply.params, apply.fun,
              data = x, nodes = nodes, alpha = alpha, B = B,
              whitelist = whitelist, blacklist = blacklist, test = test,
              debug = debug)
  names(pc) = nodes
  
  mb = lapply(nodes, function(x) {list(mb=pcs[[x]], nbr=pc[[x]])})
  names(mb) = nodes

  # check neighbourhood sets for consistency.
  mb = bn.recovery(mb, nodes = nodes, strict = strict, debug = debug)

  return(mb)

}#MAXMIN.PC

maxmin.pc.forward.phase = function(x, data, nodes, alpha, B, whitelist,
  blacklist, backtracking = NULL, test, debug = FALSE) {

  nodes = nodes[nodes != x]
  known.good = known.bad = c()
  whitelisted = nodes[sapply(nodes,
          function(y) { is.whitelisted(whitelist, c(x, y), either = TRUE) })]
  blacklisted = nodes[sapply(nodes,
          function(y) { is.blacklisted(blacklist, c(x, y), both = TRUE) })]
  cpc = c()
  association = structure(numeric(length(nodes)), names = nodes)
  to.add = ""

  # growing phase
  if (debug) {

    cat("----------------------------------------------------------------\n")
    cat("* forward phase for node", x, ".\n")

  }#THEN

  # whitelisted nodes are included, and blacklisted nodes are excluded.
  cpc = whitelisted
  nodes = nodes[!(nodes %in% c(cpc, blacklisted))]

  # use backtracking for a further screening of the nodes to be checked.
  if (!is.null(backtracking)) {

    # X adjacent to Y <=> Y adjacent to X
    known.good = names(backtracking[backtracking])
    cpc = unique(c(cpc, known.good))

    # and vice versa X not adjacent to Y <=> Y not adjacent to X
    known.bad = names(backtracking[!backtracking])

    # both are not to be checked for inclusion/exclusion.
    nodes = nodes[!(nodes %in% names(backtracking))]

    if (debug) {

      cat("    * known good (backtracking): '", known.good, "'.\n")
      cat("    * known bad (backtracking): '", known.bad, "'.\n")
      cat("    * nodes still to be tested for inclusion: '", nodes, "'.\n")

    }#THEN

  }#THEN

  # phase I (stepwise forward selection)
  repeat {

    # do not check nodes which have a p-value above the alpha
    # threshold, as it can only increase; do not check both 'known
    # bad' and 'known good' ones.
    to.be.checked = setdiff(names(which(association < alpha)), c(cpc, known.bad))
    
    # heuristic 1 : sort by name to be deterministic
    to.be.checked = to.be.checked[order(to.be.checked)]

    association = sapply(to.be.checked, maxmin.pc.heuristic.optimized, y = x,
                    sx = cpc, data = data, test = test, alpha = alpha, B = B,
                    association = association, debug = debug)
    
    # stop if there are no candidates for inclusion.
    if (all(association > alpha) || length(nodes) == 0 || is.null(nodes)) break

    # get the one which maximizes the association measure.
    to.add = names(which.min(association))

    if (debug) {

      cat("  @", to.add, "accepted as a parent/children candidate ( p-value:",
        association[to.add], ").\n")
      cat("  > current candidates are '", c(cpc, to.add), "'.\n")

    }#THEN

    if (association[to.add] <= alpha) {

      cpc = c(cpc, to.add)
      nodes = nodes[nodes != to.add]

    }#THEN

  }#REPEAT

  return(cpc)

}#MAXMIN.PC.FORWARD.PHASE

maxmin.pc.backward.phase = function(t, pcs, data, nodes, alpha, B = NULL,
  whitelist, blacklist, backtracking = NULL, test, debug = FALSE) {
  
  blacklisted = nodes[vapply(nodes, function(x) {
    is.blacklisted(blacklist, c(t, x), both = TRUE) }, logical(1))]
  whitelisted = nodes[vapply(nodes, function(x) {
    is.whitelisted(whitelist, c(t, x), either = TRUE) }, logical(1))]
  known.good = vector()
  known.bad = vector()
  
  # use backtracking for a further screening of the nodes to be checked.
  if (!is.null(backtracking)) {
    
    # X adjacent to Y <=> Y adjacent to X
    known.good = names(backtracking[backtracking])
    
    # and vice versa X not adjacent to Y <=> Y not adjacent to X
    known.bad = names(backtracking[!backtracking])
    
  }#THEN
  
  if (debug) {
    
    cat("----------------------------------------------------------------\n")
    cat("* backward phase for node", t, ".\n")
    cat(" * blacklisted nodes: '", blacklisted, "'\n")
    cat(" * whitelisted nodes: '", whitelisted, "'\n")
    
    if (!is.null(backtracking)) {
      cat(" * known good (backtracking): '", known.good, "'.\n")
      cat(" * known bad (backtracking): '", known.bad, "'.\n")
    }#THEN
    
    cat(" * starting with neighbourhood : '", pcs, "'\n")
    
  }#THEN
  
  # known good nodes are added and known bad ones are removed
  pcs = setdiff(pcs, known.bad)
  pcs = union(pcs, known.good)
  
  # whitelisted nodes are added and blacklisted ones are removed
  pcs = setdiff(pcs, blacklisted)
  pcs = union(pcs, whitelisted)
  
  # Known good and whitlisted nodes must not be checked for exclusion
  nodes.to.dsep = setdiff(pcs, c(known.good, whitelisted))
  
  for (x in nodes.to.dsep) {
    
    # excluding the node to be tested for exclusion from the conditioning set
    dsep.set = setdiff(pcs, x)
    dsep = FALSE
    
    # try to d-separate with all the possible conditioning subsets
    for (k in 0:length(dsep.set)) {
      
      # create all possible subsets of the conditioning set of size k.
      dsep.subsets = subsets(length(dsep.set), k, dsep.set)
      
      for (s in 1:nrow(dsep.subsets)) {
        
        a = conditional.test(t, x, dsep.subsets[s,], data = data, test = test,
                             B = B, alpha = alpha, debug = debug)
        
        if (a > alpha) {
          
          if (debug) {
            cat("  @ node", x, "is not a neighbour of", t, " any more\n")
          }#THEN
          
          pcs = setdiff(pcs, x)
          
          dsep = TRUE
          break
          
        }#THEN
        
      }#FOR
      
      if (dsep)
        break
      
    }#FOR
    
  }#FOR
  
  return(pcs)
  
}#MAXMIN.PC.BACKWARD.PHASE

maxmin.pc.heuristic.optimized = function(x, y, sx, data, test, alpha, B,
    association, debug = FALSE) {

  k = 0
  min.assoc = association[x]

  if (debug) {

    cat("  * checking", x ,"for max-min association, starting with", min.assoc, ".\n")

  }#THEN

  # generate only the subsets of the current parent/children set
  # which include node added last; the rest are considered to be
  # already tested against.
  last = sx[length(sx)]
  sx = sx[-length(sx)]

  repeat {

    # create all the possible subsets of size k of the candidate
    # parent-children set.
    dsep.subsets = subsets(length(sx), k, sx)

    for (s in 1:nrow(dsep.subsets)) {

      a = conditional.test(x, y, c(dsep.subsets[s,], last), data = data,
            test = test, B = B, alpha = alpha, debug = debug)

      # minimum association means maximum p-value.
      min.assoc = max(min.assoc, a)

      # if the p-value is already this high, it's useless to do further
      # testing (as it min.assoc can only increase in value).
      if (min.assoc > alpha) break

    }#FOR

    # if the p-value is already this high, it's useless to do further
    # testing (as it min.assoc can only increase in value).
    if (min.assoc > alpha) break

    if (k < length(sx))
      k = k + 1
    else
      break

  }#REPEAT

  if (debug)
    cat("  > node", x, "has a minimum association of", min.assoc, ".\n")

  return(min.assoc)

}#MAXMIN.PC.HEURISTIC.OPTIMIZED
