
# 0-degree reverse mmpc
g.pc.0 = function(t, data, whitelist, blacklist, test, alpha,
  B, backtracking = NULL, debug = FALSE) {

  nodes = names(data)

  # 1. [PCS] Get the 0-degree and the restricted (max-min) PCS
  tmp = g.pc.maxmin.pcs(t, data = data, nodes = nodes,
        alpha = alpha, B = B, whitelist = whitelist, blacklist = blacklist,
        test = test, backtracking = backtracking, debug = debug)
  pcs0 = tmp$pcs0
  pcs = tmp$pcs
  dsep = tmp$dsep

  # 2. [RSPS] Get the associated remaining spouses superset, those not already in PCS
  rsps = hybrid.pc.de.rsps(t, data, nodes, pcs, dsep, alpha, B, test, debug)
  rsps0 = hybrid.pc.de.rsps(t, data, nodes, pcs0, dsep, alpha, B, test, debug)

  # Special case : 0 or 1 nodes in PCS0
  if(length(pcs0) < 2)
    return(list(nbr = c(pcs0), mb = c(pcs0, rsps0)))

  # 3. [PC] Filter the true parents and children from PCS
  pc = hybrid.pc.filter(t, pcs, rsps, data, alpha, B, whitelist,
        blacklist, backtracking, test, debug)

  # 4. [Neighbourhood OR] Detect and add false-negatives to PC, by checking if
  #     the target is present in potential neighbours' neighbours
  for (node in pcs0[!pcs0 %in% pc]) {

    tmp = g.pc.maxmin.pcs(node, data = data, nodes = c(t, pcs0, rsps0),
          alpha = alpha, B = B, whitelist = whitelist, blacklist = blacklist,
          test = test, backtracking = NULL, debug = debug)
    pcsn = tmp$pcs
    dsepn = tmp$dsep

    rspsn = hybrid.pc.de.rsps(node, data, nodes = c(t, pcs0, rsps0), pcsn, dsepn, alpha, B, test, debug)

    pcn = hybrid.pc.filter(t = node, pcs = pcsn, rsps = rspsn, data, alpha, B,
          whitelist, blacklist, backtracking = NULL, test, debug)

    # Logical OR : add the nodes from my PCS which I don't see
    # in my PC but which see me in theirs
    if(t %in% pcn) {

      pc = c(pc, node)
      mb = c(mb, node)

      if (debug)
        cat("    @", node, "added to the parents and children. (GPC's OR)\n")

    }#THEN

  }#FOR

  res = list(nbr = pc, mb = mb)

  return(res)

}#G.PC.0

# 1-degree reverse mmpc
g.pc.1 = function(t, data, whitelist, blacklist, test, alpha,
  B, backtracking = NULL, debug = FALSE) {

  nodes = names(data)

  tmp = hybrid.pc.de.pcs(t, data, nodes, alpha, B, whitelist, blacklist,
        backtracking, test, debug)
  pcs1 = tmp$pcs
  dsep1 = tmp$dsep

  rsps1 = hybrid.pc.de.rsps(t, data, nodes, pcs1, dsep1, alpha, B, test, debug)

  # Special case : 0 or 1 nodes in PCS0
  if(length(pcs1) < 2)
    return(list(nbr = c(pcs1), mb = c(pcs1, rsps1)))

  # 1. [PCS] Get the 0-degree and the restricted (max-min) PCS
  tmp = g.pc.maxmin.pcs(t, data = data, nodes = pcs1, alpha = alpha, B = B,
        whitelist = whitelist, blacklist = blacklist, test = test,
        backtracking = backtracking, debug = debug)
  pcs = tmp$pcs
  dsep = tmp$dsep

  # 2. [RSPS] Get the associated remaining spouses superset, those not already in PCS
  rsps = hybrid.pc.de.rsps(t, data, nodes, pcs, dsep, alpha, B, test, debug)

  # 3. [PC] Filter the true parents and children from PCS
  pc = hybrid.pc.filter(t, pcs, rsps, data, alpha, B, whitelist,
        blacklist, backtracking = backtracking, test, debug)

  # 4. [Neighbourhood OR] Detect and add false-negatives to PC, by checking if
  #     the target is present in potential neighbours' neighbours
  for (node in pcs1[!pcs1 %in% pc]) {

    tmp = g.pc.maxmin.pcs(node, data = data, nodes = c(t, pcs1, rsps1),
          alpha = alpha, B = B, whitelist = whitelist, blacklist = blacklist,
          test = test, backtracking = NULL, debug = debug)
    pcsn = tmp$pcs
    dsepn = tmp$dsep

    rspsn = hybrid.pc.de.rsps(node, data, nodes = c(t, pcs1, rsps1), pcsn, dsepn, alpha, B, test, debug)

    pcn = hybrid.pc.filter(t = node, pcs = pcsn, rsps = rspsn, data, alpha, B,
          whitelist, blacklist, backtracking = NULL, test, debug)

    # Logical OR : add the nodes from my PCS which I don't see
    # in my PC but which see me in theirs
    if(t %in% pcn) {

      pc = c(pc, node)
      mb = c(mb, node)

      if (debug)
        cat("    @", node, "added to the parents and children. (GPC's OR)\n")

    }#THEN

  }#FOR

  res = list(nbr = pc, mb = mb)

  return(res)

}#G.PC.1

g.pc.maxmin.pcs = function(t, data, nodes, alpha, B, whitelist,
  blacklist, backtracking = NULL, test, debug = FALSE) {

  nodes = nodes[nodes != t]
  known.good = c()
  whitelisted = nodes[vapply(nodes,
          function(x) { is.whitelisted(whitelist, c(t, x), either = TRUE) }, logical(1))]
  blacklisted = nodes[vapply(nodes,
          function(x) { is.blacklisted(blacklist, c(t, x), both = TRUE) }, logical(1))]

  # use backtracking for a further screening of the nodes to be tested.
  # don't use known bad nodes, we will check them anyway because of
  # GPC's OR filter on neighbours
  if (!is.null(backtracking))
    known.good = names(backtracking[backtracking])

  # whitelisted and known.good nodes are included, while blacklisted nodes are
  # excluded.
  cpc = unique(c(vector(), whitelisted, known.good)) # vector() prevents a NULL
  to.be.tested.in = nodes[!(nodes %in% c(cpc, blacklisted))]
  to.be.tested.out = vector()
  min.assoc = as.list(structure(numeric(length(to.be.tested.in)), names = to.be.tested.in))
  dsep = list()

  if (debug) {

    cat("----------------------------------------------------------------\n")
    cat("* mixed forward phase for node", t, ".\n")
    if (!is.null(backtracking))
      cat("    * known good (backtracking): '", known.good, "'.\n")
    cat("    * nodes to be tested for inclusion: '", to.be.tested.in, "'.\n")

  }#THEN

  oldcpc = NULL
  pcs0 = vector()
  repeat {

    # [Step I] Check nodes not in CPC to add new positives
    max.assoc.node = NULL
    max.assoc.pval = 1

    for(node in to.be.tested.in) {

      # get each node's minimum correlation (maximum p-value)
      node.min.assoc = g.pc.least.correlation(x = t, y = node, sx = cpc, data = data,
            test = test, alpha = alpha, B = B, min.assoc = min.assoc[[node]],
            debug = debug)

      min.assoc[[node]] = node.min.assoc$pval
      dsep[[node]] = node.min.assoc$dsep

      # do not check nodes which have a maximum p-value above the alpha
      # threshold, as it can only increase
      if(node.min.assoc$pval > alpha) {
        to.be.tested.in = setdiff(to.be.tested.in, node)
        next
      }#THEN

      # keep the least least correlated node (minimum maximum p-value)
      if(is.null(max.assoc.node) | node.min.assoc$pval < max.assoc.pval) {
        max.assoc.node = node
        max.assoc.pval = node.min.assoc$pval
      }#THEN

      # in the first round, keep the pcs (0-degree subset)
      if(is.null(oldcpc))
        pcs0 = c(pcs0, node)

    }#FOR

    # add the least least correlated node
    if(!is.null(max.assoc.node)) {

      cpc = c(cpc, max.assoc.node)
      to.be.tested.in = setdiff(to.be.tested.in, max.assoc.node)
      to.be.tested.out = cpc[!cpc %in% c(whitelisted, known.good, max.assoc.node)]

      if (debug) {

        cat("  @", max.assoc.node, "accepted as a parent/children candidate ( p-value:",
              max.assoc.pval, ").\n")
        cat("  > current candidates are '", cpc, "'.\n")

      }#THEN

    }#THEN

    # [Step II] Check nodes in CPC to early detect false-positive nodes
    min.assoc.node = NULL
    min.assoc.pval = 0

    # optimisation : don't test the lastly added node
    for(node in to.be.tested.out) {

      # get each node's least correlation (maximum p-value)
      node.min.assoc = g.pc.least.correlation(x = t, y = node, sx = setdiff(cpc, node), data = data,
            test = test, alpha = alpha, B = B, min.assoc = min.assoc[[node]],
            debug = debug)

      min.assoc[[node]] = node.min.assoc$pval
      dsep[[node]] = node.min.assoc$dsep

      # keep the most least correlated node (maximum maximum p-value)
      if(is.null(min.assoc.node) | node.min.assoc$pval > min.assoc.pval) {
        min.assoc.node = node
        min.assoc.pval = node.min.assoc$pval
      }#THEN

    }#FOR

    # remove the most least correlated node if it's p-value is above the alpha
    # threshold
    if(!is.null(min.assoc.node) & min.assoc.pval > alpha) {

      cpc = setdiff(cpc, min.assoc.node)
      to.be.tested.out = setdiff(to.be.tested.out, min.assoc.node)

      if (debug) {
        cat("  @", min.assoc.node, "removed from parent/children candidates ( p-value:",
              min.assoc.pval, "with subset", dsep[[min.assoc.node]], ").\n")
        cat("  > current candidates are '", cpc, "'.\n")
      }#THEN

      # for nodes which had their minimum correlation conditionned by the
      # removed node, we trigger a re-computation of the minimum correlation
      for(node in c(to.be.tested.in, to.be.tested.out))
        if(min.assoc.node %in% dsep[[node]]) {
          dsep[[node]] = NULL
          min.assoc[[node]] = NULL
        }#THEN

    }#THEN
    else {
      to.be.tested.out = vector()
    }#ELSE

    # stop when the CPC set does not change
    if(setequal(oldcpc, cpc))
      break

    oldcpc = cpc

  }#REPEAT

  res = list(
    pcs0 = pcs0,
    pcs = cpc,
    dsep = dsep)
  return(res)

}#G.PC.MAXMIN.PCS

g.pc.least.correlation = function(x, y, sx, data, test, alpha, B, min.assoc,
      debug = FALSE) {

  min.dsep.set = NULL
  last = NULL

  if (debug) {

    cat("  * checking node", y ,"for association.\n")
    cat("    > starting with association", min.assoc, ".\n")

  }#THEN

  # a null min.assoc means that all the possible subsets have to be (re)tested
  if(!is.null(min.assoc)) {

    # generate only the subsets of the current parent/children set
    # which include node added last; the rest are considered to be
    # already tested against.
    last = sx[length(sx)]
    sx = sx[-length(sx)]

  }

  for (k in 0:length(sx)) {

    # create all the possible subsets of size k of the candidate
    # parent-children set.
    dsep.subsets = subsets(length(sx), k, sx)

    for (s in 1:nrow(dsep.subsets)) {

      a = conditional.test(x, y, c(dsep.subsets[s,], last), data = data,
            test = test, B = B, alpha = alpha)

      if (debug) {

        cat("    > trying conditioning subset '", c(dsep.subsets[s,], last), "'.\n")

      }#THEN

      # minimum association means maximum p-value.
      min.assoc = max(min.assoc, a)
      if(min.assoc == a) {
        min.dsep.set = c(dsep.subsets[s,], last)
      }

      # if the p-value is already this high, it's useless to do further
      # testing (as it min.assoc can only increase in value).
      if (min.assoc > alpha) break

    }#FOR

    # if the p-value is already this high, it's useless to do further
    # testing (as it min.assoc can only increase in value).
    if (min.assoc > alpha) break

  }#FOR

  if (debug)
    cat("    > node", y, "has a minimum association of", min.assoc,
          "with subset", min.dsep.set, ".\n")

  res = list(
    pval = min.assoc,
    dsep = min.dsep.set)
  return(res)

}#G.PC.LEAST.CORRELATION
