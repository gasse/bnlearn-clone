r.pc.0 = function(t, data, whitelist, blacklist, test, alpha,
  B, backtracking = NULL, debug = FALSE) {

  nodes = names(data)

  # 1. [PCS] Get the 0-degree PCS
  tmp = r.pc.de.pcs.0(t, data, nodes, alpha, B, whitelist, blacklist,
        backtracking = backtracking, test = test, debug = debug)
  pcs = tmp$pcs
  dsep = tmp$dsep

  # 2. [RSPS] Get remaining spouses superset, those not already in PCS
  rsps = hybrid.pc.de.rsps(t, data, nodes, pcs, dsep, alpha, B, test, debug)

  # Special case : 0 or 1 nodes in PCS
  if(length(pcs) < 2)
    return(list(nbr = c(pcs), mb = c(pcs, rsps)))

  # 3. [PC] Filter the true parents and children from PCS
  pc = hybrid.pc.filter(t, pcs, rsps, data, alpha, B, whitelist,
        blacklist, backtracking = backtracking, test, debug)

  # 4. [Neighbourhood OR] Detect and add false-negatives to PC, by checking if
  #     the target is present in potential neighbours' neighbours
  for (node in pcs[!pcs %in% pc]) {

    tmp = r.pc.de.pcs.0(node, data, nodes = c(t, pcs, rsps), alpha, B,
          whitelist, blacklist, backtracking = backtracking, test = test,
          debug = debug)
    pcsn = tmp$pcs
    dsepn = tmp$pcs

    rspsn = hybrid.pc.de.rsps(node, data, nodes = c(t, pcs, rsps), pcsn, dsepn,
          alpha, B, test, debug)

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

}#R.PC.0

r.pc.1 = function(t, data, whitelist, blacklist, test, alpha,
  B, backtracking = NULL, debug = FALSE) {

  nodes = names(data)

  # 1. [PCS] Get the 0-degree PCS
  tmp = hybrid.pc.de.pcs(t, data, nodes, alpha, B, whitelist, blacklist,
        backtracking = backtracking, test = test, debug = debug)
  pcs = tmp$pcs
  dsep = tmp$dsep

  # 2. [RSPS] Get remaining spouses superset, those not already in PCS
  rsps = hybrid.pc.de.rsps(t, data, nodes, pcs, dsep, alpha, B, test, debug)

  # Special case : 0 or 1 nodes in PCS
  if(length(pcs) < 2)
    return(list(nbr = c(pcs), mb = c(pcs, rsps)))

  # 3. [PC] Filter the true parents and children from PCS
  pc = hybrid.pc.filter(t, pcs, rsps, data, alpha, B, whitelist,
        blacklist, backtracking = backtracking, test, debug)

  # 4. [Neighbourhood OR] Detect and add false-negatives to PC, by checking if
  #     the target is present in potential neighbours' neighbours
  for (node in pcs[!pcs %in% pc]) {

    tmp = hybrid.pc.de.pcs(node, data, nodes = c(t, pcs, rsps), alpha, B,
          whitelist, blacklist, backtracking = backtracking, test = test,
          debug = debug)
    pcsn = tmp$pcs
    dsepn = tmp$pcs

    rspsn = hybrid.pc.de.rsps(node, data, nodes = c(t, pcs, rsps), pcsn, dsepn,
          alpha, B, test, debug)

    pcn = hybrid.pc.filter(t = node, pcs = pcsn, rsps = rspsn, data, alpha, B,
          whitelist, blacklist, backtracking = NULL, test, debug)

    # Logical OR : add the nodes from my PCS which I don't see
    # in my PC but which see me in theirs
    if(t %in% pcn) {

      pc = c(pc, node)
      mb = c(mb, node)

      if (debug)
        cat("    @", node, "added to the parents and children. (RPC's OR)\n")

    }#THEN

  }#FOR

  res = list(nbr = pc, mb = mb)

  return(res)

}#R.PC.1

r.pc.de.pcs.0 = function(t, data, nodes, alpha, B, whitelist, blacklist,
  backtracking = NULL, test, debug = FALSE) {

  known.good = c()
  whitelisted = nodes[vapply(nodes,
          function(x) { is.whitelisted(whitelist, c(t, x), either = TRUE) }, logical(1))]
  blacklisted = nodes[vapply(nodes,
          function(x) { is.blacklisted(blacklist, c(t, x), both = TRUE) }, logical(1))]

  # use backtracking for a further screening of the nodes to be checked.
  # don't use known bad nodes, we will check them anyway because of
  # HPC's OR filter on neighbours
  if (!is.null(backtracking)) {
    known.good = names(backtracking[backtracking])
  }

  if (debug) {

    cat("----------------------------------------------------------------\n")
    cat("* learning the 0-degree PCS of", t, ".\n")
    cat("    * known good (backtracking): '", known.good, "'.\n")
    cat("    * nodes still to be tested for inclusion: '",
          nodes[!(nodes %in% c(t, known.good))], "'.\n")

  }#THEN

  # Phase (I): remove X if Ind(T,X) (0-degree d-separated nodes)
  pcs = nodes[!(nodes %in% c(t, known.good, whitelisted, blacklisted))]
  pvalues = vector()
  dsep = list()
  for (x in pcs) {

    a = conditional.test(t, x, c(), data = data, test = test, B = B,
          alpha = alpha, debug = debug)

    if (a > alpha) { 

      pcs = pcs[pcs != x]
      dsep[[x]] = c()

      if (debug)
        cat("    > node", x, "removed from the parents and children superset. ( p-value:", a, ")\n")

    }#THEN
  }#FOR
  
  pcs = unique(c(pcs, known.good, whitelisted))

  if(debug)
    cat("    * resulting PCS: '", pcs, "'\n")

  ret = list(pcs=pcs, dsep=dsep)
  return(ret)

}#R.PC.DE.PCS.0
