
# TODO : support cache for the last S statistic calls?
# TODO : improve backtracking by adding it in the OR phase?

hybrid.pc = function(t, data, whitelist, blacklist, test, alpha,
  B, backtracking = NULL, debug = FALSE) {

  nodes = names(data)

  # 1. [PCS] Search parents and children superset
  tmp = hybrid.pc.de.pcs(t, data, nodes, alpha, B, whitelist, blacklist,
        backtracking, test, debug)
  pcs = tmp$pcs
  dsep = tmp$dsep

  # 2. [RSPS] Search remaining spouses superset, those not already in PCS
  rsps = hybrid.pc.de.rsps(t, data, nodes, pcs, dsep, alpha, B, test, debug)
  
  # Special case : 0 or 1 nodes in PC
  if(length(c(pcs, rsps)) < 2)
      return(list(nbr = c(pcs, rsps), mb = c(pcs, rsps)))

  # 3. [IAMB] Get the Markov boundary from nodes within PCS and RSPS
  mb = inter.ia.markov.blanket(t, data, nodes = c(t, pcs, rsps), alpha, B,
        whitelist, blacklist, backtracking, test, debug)

  # 4. [PC] Filter the true parents and children from the MB
  pc = hybrid.pc.filter(t, pcs = mb, rsps = NULL, data, alpha, B, whitelist,
        blacklist, backtracking, test, debug)

  # 5. [Neighbourhood OR] Detect and add false-negatives to PC, by checking if
  #     the target is present in potential neighbours' neighbours
  for (node in pcs[!pcs %in% pc]) {

    mbn = inter.ia.markov.blanket(node, data, nodes = c(t, pcs, rsps), alpha,
          B, whitelist, blacklist, backtracking = NULL, test, debug)

    pcn = hybrid.pc.filter(t = node, pcs = mbn, rsps = NULL, data, alpha, B,
          whitelist, blacklist, backtracking = NULL, test, debug)

    # Logical OR : add the nodes from my PCS which I don't see
    # in my PC but which see me in theirs
    if(t %in% pcn) {

      pc = c(pc, node)
      mb = c(mb, node)

      if (debug)
        cat("  @", node, "added to the parents and children. (HPC's OR)\n")

    }#THEN

  }#FOR

  if (debug)
    cat("  * PC =", pc, "\n")

  res = list(nbr = pc, mb = c(pcs, rsps))

  return(res)

}#HYBRID.PC

# PCS + RSP filtering for neighbours too
hybrid.pc.2 = function(t, data, whitelist, blacklist, test, alpha,
  B, backtracking = NULL, debug = FALSE) {

  nodes = names(data)

  # 1. [PCS] Search parents and children superset
  tmp = hybrid.pc.de.pcs(t, data, nodes, alpha, B, whitelist, blacklist,
        backtracking, test, debug)
  pcs = tmp$pcs
  dsep = tmp$dsep

  # 2. [RSPS] Search remaining spouses superset, those not already in PCS
  rsps = hybrid.pc.de.rsps(t, data, nodes, pcs, dsep, alpha, B, test, debug)
  
  # Special case : 0 or 1 nodes in PC
  if(length(c(pcs, rsps)) < 2)
      return(list(nbr = c(pcs, rsps), mb = c(pcs, rsps)))

  # 3. [IAMB] Get the Markov boundary from nodes within PCS and RSPS
  mb = inter.ia.markov.blanket(t, data, nodes = c(t, pcs, rsps), alpha, B,
        whitelist, blacklist, backtracking, test, debug)

  # 4. [PC] Filter the true parents and children from the MB
  pc = hybrid.pc.filter(t, pcs = mb, rsps = NULL, data, alpha, B, whitelist,
        blacklist, backtracking, test, debug)

  # 5. [Neighbourhood OR] Detect and add false-negatives to PC, by checking if
  #     the target is present in potential neighbours' neighbours
  for (node in pcs[!pcs %in% pc]) {

    tmp = hybrid.pc.de.pcs(node, data, c(t, pcs, rsps), alpha, B, whitelist,
          blacklist, backtracking = NULL, test, debug)
    pcsn = tmp$pcs
    dsepn = tmp$dsep

    rspsn = hybrid.pc.de.rsps(node, data, c(t, pcs, rsps), pcsn, dsepn, alpha,
          B, test, debug)

    mbn = inter.ia.markov.blanket(node, data, nodes = c(t, pcsn, rspsn), alpha,
          B, whitelist, blacklist, backtracking = NULL, test, debug)

    pcn = hybrid.pc.filter(t = node, pcs = mbn, rsps = NULL, data, alpha, B,
          whitelist, blacklist, backtracking = NULL, test, debug)

    # Logical OR : add the nodes from my PCS which I don't see
    # in my PC but which see me in theirs
    if(t %in% pcn) {

      pc = c(pc, node)

      if (debug)
        cat("    @", node, "added to the parents and children. (HPC's OR)\n")

    }#THEN

  }#FOR

  res = list(nbr = pc, mb = c(pcs, rsps))

  return(res)

}#HYBRID.PC.2

hybrid.pc.de.pcs = function(t, data, nodes, alpha, B, whitelist, blacklist,
  backtracking = NULL, test, debug = FALSE) {

  known.good = c()
  whitelisted = nodes[vapply(nodes,
          function(x) { is.whitelisted(whitelist, c(t, x), either = TRUE) }, logical(1))]
  blacklisted = nodes[vapply(nodes,
          function(x) { is.blacklisted(blacklist, c(t, x), both = TRUE) }, logical(1))]
  pcs = vector()
  pvalues = vector()
  dsep = list()

  if (debug) {
    cat("----------------------------------------------------------------\n")
    cat("* learning the PCS of", t, ".\n")
  }#THEN

  # use backtracking for a further screening of the nodes to be checked.
  # don't use known bad nodes, we want to check them anyway because of
  # HPC's OR filter on neighbours
  if (!is.null(backtracking)) {

    known.good = names(backtracking[backtracking])

    if(debug) {
      cat(" * known good (backtracking): '", known.good, "'.\n")
    }#THEN

  }#THEN

  if (debug) {
    cat(" * nodes to be tested for inclusion: '",
          nodes[!(nodes %in% c(t, known.good))], "'.\n")
  }#THEN

  # heuristic 1 : sort by name to be deterministic
  nodes.to.check = nodes[!(nodes %in% c(t, known.good, whitelisted, blacklisted))]
  nodes.to.check = nodes.to.check[order(nodes.to.check)]

  # Phase (I): remove X if Ind(T,X) (0-degree d-separated nodes)
  for (x in nodes.to.check) {

    a = conditional.test(t, x, c(), data = data, test = test, B = B,
          alpha = alpha, debug = debug)

    if (a <= alpha) {

      if (debug)
        cat("  @ node", x, "added to the parents and children superset\n")

      # keep pcs with p-values in order to order nodes in the next phase
      pcs = c(pcs, x)
      pvalues = c(pvalues, a)

    }#THEN

  }#FOR

  # heuristic 2 : sort the candidates in decreasing p-value order
  # this way we are more prone to remove less correlated nodes first
  pcs = pcs[order(pvalues, decreasing = TRUE)]

  pcs = c(known.good[!known.good %in% pcs], pcs)
  pcs = c(whitelisted[!whitelisted %in% pcs], pcs)

  if (debug) {
    cat(" * nodes to be tested for exclusion: '",
          pcs[!(pcs %in% c(known.good, whitelisted))], "'.\n")
  }#THEN

  # Phase (II): remove X if Ind(T,X|Y) (1-degree d-separated nodes)
  for (x in pcs[!(pcs %in% c(known.good, whitelisted))])
    for (y in pcs[pcs != x]) {

      a = conditional.test(t, x, c(y), data = data, test = test, B = B,
            alpha = alpha, debug = debug)

      if (a > alpha) {

        pcs = pcs[pcs != x]
        dsep[[x]] = c(y)

        if (debug) {

          cat("  @ node", x, "removed from the parents and children superset\n")

        }#THEN

        break

      }#THEN
    }#FOR

  if(debug)
    cat(" * PCS =", pcs, "\n")

  ret = list(pcs=pcs, dsep=dsep)
  return(ret)

}#HYBRID.PC.DE.PCS

hybrid.pc.de.rsps = function(t, data, nodes, pcs, dsep, alpha, B, test,
  debug = FALSE) {

  rsps = vector()

  if (debug) {

    cat("----------------------------------------------------------------\n")
    cat("* learning the RSPS of", t, ".\n")
    cat(" * PCS =", pcs, "\n")
    cat(" * nodes still to be tested for inclusion: ", nodes[!(nodes %in% c(t, pcs))], "\n")

  }#THEN

  for (x in pcs) {

    rspsx = vector()
    pvaluesx = vector()
    
    # heuristic 1 : sort by name to be deterministic
    nodes.to.check = nodes[!nodes %in% c(t, pcs)]
    nodes.to.check = nodes.to.check[order(nodes.to.check)]

    # Phase (I): search spouses Y in the form T->X<-Y from the
    # remaining nodes (not in pcs)
    for (y in nodes.to.check) {

      # optimisation : avoid irrelevant tests
      if (x %in% dsep[[y]])
        next

      a = conditional.test(t, y, c(dsep[[y]], x), data = data, test = test,
            B = B, alpha = alpha, debug = debug)

      if (a <= alpha) {

        rspsx = c(rspsx, y)
        pvaluesx = c(pvaluesx, a)

        if (debug) {

          cat("  @ node", y, "added to the spouses superset by", x, "\n")

        }#THEN
      
      }#THEN
    }#FOR

    # heuristic 2 : sort the candidates in decreasing p-value order
    # this way we are more prone to remove less correlated nodes first
    rspsx = rspsx[order(pvaluesx, decreasing = TRUE)]

    # Phase (II): remove false positive spouses Y in the form T->X<-Z<-...<-Y
    # (descendants or ancestors of Z)
    for (y in rspsx)
      for (z in rspsx[rspsx != y]) {

        a = conditional.test(t, y, c(x, z), data = data, test = test, B = B,
              alpha = alpha, debug = debug)

        if (a > alpha) {

          rspsx = rspsx[rspsx != y]

          if (debug) {

            cat("  @ node", y, "removed from the spouses superset by", z, "\n")

          }#THEN
          
          break
        
        }#THEN
      }#FOR

    rsps = c(rsps, rspsx)
    
  }#FOR

  rsps = unique(rsps)

  if(debug)
    cat(" * RSPS =", rsps, "\n")

  return(rsps)

}#HYBRID.PC.DE.RSPS

# Build the parents and children (PC) set of a node from it's parents and
# children superset (PCS) and it's remaining spouses superset (RSPS).
# we assume intersection(t, pcs, rsps) is empty
hybrid.pc.filter = function(t, pcs, rsps, data, alpha, B = NULL, whitelist, blacklist,
  backtracking = NULL, test, debug = FALSE) {

  # markov boundary superset (markov blanket)
  mbs = c(pcs, rsps)

  known.good = c()
  blacklisted = mbs[vapply(mbs,
          function(x) { is.blacklisted(blacklist, c(t, x), both = TRUE) }, logical(1))]
  whitelisted = mbs[vapply(mbs,
          function(x) { is.whitelisted(whitelist, c(t, x), either = TRUE) }, logical(1))]

  # use backtracking for a further screening of the nodes to be checked.
  # known bad nodes are not used, we want to keep it possible to add them,
  # because of HPC's OR filter on neighbours
  if (!is.null(backtracking)) {

    # neighbourhood is symmetric, so X \in N(Y) <=> Y \in N(X)
    known.good = names(backtracking[backtracking])

  }#THEN

  if (debug) {

    cat("----------------------------------------------------------------\n")
    cat("* filtering PC of", t, ".\n")
    cat(" * blacklisted nodes: '", blacklisted, "'\n")
    cat(" * whitelisted nodes: '", whitelisted, "'\n")
    cat(" * starting with neighbourhood superset: '", pcs, "'\n")
    cat(" * with remaining spouses superset: '", rsps, "'\n")

    if (!is.null(backtracking))
      cat(" * known good (backtracking): '", known.good, "'.\n")

  }#THEN

  # blacklisted nodes are removed if both directed arcs are banned
  pcs = pcs[!(pcs %in% blacklisted)]
  
  pc = vector()
  if (length(mbs) > 0) {

    nbr = function(x) {

      # excluding the node to be tested for exclusion from the conditioning set
      dsep.set = setdiff(mbs, x)

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
            }

            return(FALSE)

          }#THEN

        }#FOR

      }#REPEAT

      # all tests failed, the nodes could not be d-separated
      return(TRUE)

    }#NBR

    # apply the PC filtering
    # do not even try to remove whitelisted and backtracked (good) nodes.
    canpc = pcs[!(pcs %in% c(whitelisted, known.good))]
    pc = canpc[vapply(canpc, nbr, logical(1))]

    # whitelisted nodes are included (arc orientation is irrelevant),
    # same for known good nodes
    pc = unique(c(pc, whitelisted, known.good))

    if (debug)
      cat(" * PC =", pc, "\n")

  }#THEN

  return(pc)

}#HYBRID.PC.FILTER