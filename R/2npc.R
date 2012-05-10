#TODO : add whitelist / blacklist support
#TODO : add backtracking support

twoneighbourhood.pc = function(t, data, whitelist, blacklist, test, alpha, B,
  backtracking = NULL, debug = FALSE) {

  nodes = names(data)

  pcs = vector()
  pcs.max.pval = vector()
  pcs.to.remove = vector()
  rsps = list()
  dsep = list()

  # Step I - 0 degree filtering
  #   build neighbourhood superset

  if(debug) {
    cat("----------------------------------------------------------------\n")
    cat("* 0 degree filtering\n")
  }#THEN

  # build neighbourhood superset
  for (x in setdiff(nodes, t)) {

     # is X a neighbour of T ?
    a = conditional.test(t, x, c(), data = data, test = test, B = B, alpha = alpha, debug = debug)
    if (a <= alpha) {

      if (debug)
        cat("  >", t ,"and", x, "are now neighbours\n")

      # add new neighbour
      pcs = c(pcs, x)
      pcs.max.pval[x] = a

    }#THEN
    else {

      # keep trace of the d-separator set
      dsep[[x]] = vector()

    }#ELSE

  }#FOR

  if (debug)
    cat("  >", t, "parents and children superset = '", pcs, "'\n")

  # Special case : 0 or 1 nodes in PCS
  if (length(pcs) < 2)
    return(list(nbr = pcs, mb = nodes, pcs))

  # Step II - 1 degree filtering
  #   build spouses superset
  #   restrict neighbourhood superset

  if(debug) {
    cat("* 1 degree filtering\n")
  }#THEN

  # heuristic : order neighbours from lower to higher correlated
  # this way we are more prone to remove less correlated nodes first
  ord = order(pcs.max.pval, decreasing = TRUE)
  pcs = pcs[ord]
  pcs.max.pval = pcs.max.pval[ord]

  # restrict neighbourhood superset
  for (x in setdiff(pcs, pcs.to.remove)) {
    for(y in setdiff(pcs, x)) {

      if(debug) {
        cat("* trying to d-separate", x, "and", t, "with 1 degree filtering\n")
      }#THEN

      # is X still a neighbour of T ?
      a = conditional.test(t, x, y, data = data, test = test, B = B, alpha = alpha, debug = debug)
      pcs.max.pval[x] = max(pcs.max.pval[x], a)
      if (a > alpha) {

        if(debug) {
          cat("*", x, "and", t, "should not be neighbours from", t, "'s point of view\n")
        }#THEN

        # tag neighbour to be removed
        pcs.to.remove = c(pcs.to.remove, x)

        break

      }#THEN

    }#FOR
  }#FOR

  # heuristic : order neighbours from lower to higher correlated
  # this way we are more prone to remove less correlated nodes first
  ord = order(pcs.max.pval, decreasing = TRUE)
  pcs = pcs[ord]
  pcs.max.pval = pcs.max.pval[ord]

  k = 1
  for (x in pcs.to.remove) {

    if(debug) {
      cat("* reverse trying to d-separate", x, "and", t, "with", k, "maximum degree filtering\n")
    }#THEN

    mb = c(pcs, unique(unlist(rsps)))
    neighbour = twoneighbourhood.reverse.pcs.rsps(t = x, n = t, data, nodes = mb, kmax = k,
          alpha = alpha, B = B, whitelist = whitelist, blacklist = blacklist,
          backtracking = NULL, test = test, debug = debug)

    if (!neighbour$is.neighbour) {

      if (debug)
        cat("  >", t ,"and", x, "are not neighbours any more\n")

      pcs.to.remove = setdiff(pcs.to.remove, x)

      # remove neighbour
      pcs = setdiff(pcs, x)
      pcs.max.pval = pcs.max.pval[pcs]

      # keep trace of the d-separator set
      dsep[[x]] = neighbour$dsep

    }#THEN
    else {

      pcs.max.pval[x] = max(pcs.max.pval[x], neighbour$max.pval)

    }#ELSE

  }#FOR

  # build spouses superset
  for (x in names(dsep)) {

    if(debug) {
      cat("* trying to make", x, "and", t, "spouses\n")
    }#THEN

    for(y in setdiff(pcs, dsep[[x]])) {

      # is X a spouse of T by Y ?
      a = conditional.test(t, x, c(dsep[[x]], y), data = data, test = test, B = B, alpha = alpha, debug = debug)
      if (a <= alpha) {

        if (debug)
          cat("  >", t ,"and", x, "are now spouses by", y, "\n")

        # add spouse by Y
        rsps[[y]] = c(rsps[[y]], x)

      }#THEN

    }#FOR
  }#FOR

  if (debug) {
    cat("  >", t, "parents and children superset = '", pcs, "'\n")
    for (y in names(rsps))
      cat("  >", t, "remaining spouses superset by", y, "= '", rsps[[y]], "'\n")
  }#THEN

  # Step III - k degree filtering
  #   restrict neighbourhood superset
  #   check if old neighbours could be spouses
  #   restrict spouses superset

  k = 2
  while (k < length(pcs) + length(unique(unlist(rsps)))) {

    if(debug) {
      cat("*", k, "degree filtering\n")
    }#THEN

    # heuristic : order neighbours from lower to higher correlated
    # this way we are more prone to remove less correlated nodes first
    ord = order(pcs.max.pval, decreasing = TRUE)
    pcs = pcs[ord]
    pcs.max.pval = pcs.max.pval[ord]

    # restrict spouses superset
    for (y in names(rsps)) {
      for (x in rsps[[y]]) {

        dsep.pool = setdiff(rsps[[y]], c(dsep[[x]], x))

        # if k-degree filtering cannot be done any more, stop
        if (k - 1 > length(dsep.pool))
          break

        # try to d-separate spouse X by conditioning with subsets of size k
        # (actually subsets of sizes k-1, to which we add Y)
        first.dsep = twoneighbourhood.first.dsep(x = t, y = x,
              z = c(dsep[[x]], y), sz = dsep.pool, kmin = k - 1, kmax = k - 1,
              data = data, test = test, alpha = alpha, B = B, debug = debug)

        if (!is.null(first.dsep$pval) && first.dsep$pval > alpha) {

          if (debug)
            cat("  >", t ,"and", x, "are not spouses by", y, "any more\n")

          # remove spouse X by Y
          rsps[[y]] = setdiff(rsps[[y]], x)

        }#THEN

      }#FOR
    }#FOR

    # restrict neighbourhood superset
    # from the target's point of view
    for (x in setdiff(pcs, pcs.to.remove)) {

      if (debug)
        cat("* trying to d-separate", x, "and", t, "with", k, "degree filtering\n")

      dsep.pool = setdiff(c(pcs, unique(unlist(rsps))), x)

      # if k-degree filtering cannot be done any more, stop
      if (k > length(dsep.pool))
        break

      # try to d-separate neighbour X by conditioning with subsets of size k
      first.dsep = twoneighbourhood.first.dsep(x = t, y = x,
            z = NULL, sz = dsep.pool, kmin = k, kmax = k, data = data,
            test = test, alpha = alpha, B = B, debug = debug)

      if (!is.null(first.dsep$pval) && first.dsep$pval > alpha) {

        if (debug)
          cat("*", x, "and", t, "should not be neighbours from", x, "'s point of view\n")

        # remove neighbour
        pcs.to.remove = c(pcs.to.remove, x)

      }#THEN

    }#FOR

    # re-check restricted neighbours
    # from each neighbour's point of view
    for (x in pcs.to.remove) {

      if(debug) {
        cat("* reverse trying to d-separate", x, "and", t, "with", k, "maximum degree filtering\n")
      }#THEN

      mb = c(pcs, unique(unlist(rsps)))
      neighbour = twoneighbourhood.reverse.pcs.rsps(t = x, n = t, data, nodes = mb, kmax = k,
            alpha = alpha, B = B, whitelist = whitelist, blacklist = blacklist,
            backtracking = NULL, test = test, debug = debug)

      if (!neighbour$is.neighbour) {

        if (debug)
          cat("  >", t ,"and", x, "are not neighbours any more\n")

        pcs.to.remove = setdiff(pcs.to.remove, x)

        # remove neighbour
        pcs = setdiff(pcs, x)
        pcs.max.pval = pcs.max.pval[pcs]

        # remove spouses by this neighbour
        rsps[[x]] = NULL

        # keep trace of the d-separator set
        dsep[[x]] = neighbour$dsep

        # check if old neighbours could be spouses
        for(y in setdiff(pcs, dsep[[x]])) {

          # is X a spouse of T by Y ?
          a = conditional.test(t, x, c(dsep[[x]], y), data = data, test = test, B = B, alpha = alpha, debug = debug)
          if (a <= alpha) {

            oldrsps = rsps[[y]]
            twoneighbourhood.add.spouse(t, x, y, rsps[[y]], dsep, k, data, test, B, alpha, debug)
            if (debug) {
              if (x %in% rsps[[y]])
                cat("  >", t ,"and", x, "are now spouses by", y, "\n")
              for (sp in setdiff(oldrsps, rsps[[y]]))
                cat("  >", t ,"and", sp, "are not spouses by", y, "any more\n")
            }#THEN

          }#THEN

        }#FOR

      }#THEN
      else {

        pcs.max.pval[x] = max(pcs.max.pval[x], neighbour$max.pval)

      }#ELSE

    }#FOR

    if (debug) {
      cat("  >", t, "parents and children superset = '", pcs, "'\n")
      for (y in names(rsps))
        cat("  >", t, "remaining spouses superset by", y, "= '", rsps[[y]], "'\n")
    }#THEN

    k = k + 1

  }#WHILE

  res = list(
    nbr = pcs,
    mb = c(pcs, unique(unlist(rsps))))

  return(res)

}#TWONEIGHBOURHOOD.PC

twoneighbourhood.reverse.pcs.rsps = function(t, n, data, nodes, kmax, whitelist, blacklist, test, alpha, B,
  backtracking = NULL, debug = FALSE) {

  nodes = c(n, setdiff(nodes, n))

  pcs = vector()
  pcs.max.pval = vector()
  rsps = list()
  dsep = list()

  # Step I - 0 degree filtering
  #   build neighbourhood superset

  for (x in setdiff(nodes, t)) {

     # is X a neighbour of T ?
    a = conditional.test(t, x, c(), data = data, test = test, B = B, alpha = alpha, debug = debug)
    if (a <= alpha) {

      # add new neighbour
      pcs = c(pcs, x)
      pcs.max.pval[x] = a

    }#THEN
    else {

      # keep trace of the d-separator set
      dsep[[x]] = vector()

      if (x == n)
        return(list(
              is.neighbour = FALSE,
              max.pval = a,
              dsep = dsep[[x]]))

    }#ELSE

  }#FOR

  # Special case : maximum conditioning size = 0
  # Special case : PCS = target (alone)
  # stop here
  if (kmax == 0 | length(pcs) == 1)
    return(list(
          is.neighbour = TRUE,
          max.pval = pcs.max.pval[n],
          dsep = NULL,
          continue = length(pcs) > 1))

  # Step II - 1 degree filtering
  #   restrict neighbourhood superset
  #   build spouses superset

  # heuristic : order neighbours from lower to higher correlated
  # this way we are more prone to remove less correlated nodes first
  ord = order(pcs.max.pval, decreasing = TRUE)
  pcs = pcs[ord]
  pcs.max.pval = pcs.max.pval[ord]

  # restrict neighbourhood superset (1 degree conditioning)
  for (x in pcs) {
    for(y in setdiff(pcs, x)) {

      # is X still a neighbour of T ?
      a = conditional.test(t, x, y, data = data, test = test, B = B, alpha = alpha, debug = debug)
      if (a > alpha) {

        # remove neighbour
        pcs = setdiff(pcs, x)
        pcs.max.pval = pcs.max.pval[pcs]

        # keep trace of the d-separator set
        dsep[[x]] = y

        if (x == n)
          return(list(
                is.neighbour = FALSE,
                max.pval = a,
                dsep = dsep[[x]]))

        break

      }#THEN
      else {

        pcs.max.pval[x] = max(pcs.max.pval[x], a)

      }#ELSE

    }#FOR
  }#FOR

  # Special case : maximum conditioning size = 1
  # stop here
  if (kmax == 1)
    return(list(
          is.neighbour = TRUE,
          max.pval = pcs.max.pval[n],
          dsep = NULL))

  # build spouses superset (1 degree conditioning)
  for (x in names(dsep)) {
    for(y in setdiff(pcs, dsep[[x]])) {

      # is X a spouse of T by Y ?
      a = conditional.test(t, x, c(dsep[[x]], y), data = data, test = test, B = B, alpha = alpha, debug = debug)
      if (a <= alpha) {

        # add spouse by Y
        rsps[[y]] = c(rsps[[y]], x)

      }#THEN

    }#FOR
  }#FOR

  # Step III - k degree filtering
  #   restrict spouses superset
  #   restrict neighbourhood superset
  #   check if old neighbours could be spouses

  k = 2
  while (k < length(pcs) + length(unique(unlist(rsps))) & k <= kmax) {

    # heuristic : order neighbours from lower to higher correlated
    # this way we are more prone to remove less correlated nodes first
    ord = order(pcs.max.pval, decreasing = TRUE)
    pcs = pcs[ord]
    pcs.max.pval = pcs.max.pval[ord]

    # restrict spouses superset
    for (y in names(rsps)) {
      for (x in rsps[[y]]) {

        dsep.pool = setdiff(rsps[[y]], x)

        # if k-degree filtering cannot be done any more, stop
        if(k - 1 > length(dsep.pool))
          break

        # try to d-separate spouse X by conditioning with subsets of size k
        # (actually subsets of sizes k-1, to which we add Y)
        first.dsep = twoneighbourhood.first.dsep(x = t, y = x, z = c(dsep[[x]], y),
              sz = dsep.pool, kmin = k - 1, kmax = k - 1, data = data,
              test = test, alpha = alpha, B = B, debug = debug)

        if (!is.null(first.dsep$pval) && first.dsep$pval > alpha) {

            # remove spouse by y
            rsps[[y]] = setdiff(rsps[[y]], x)
            break

        }#THEN
      }#FOR
    }#FOR

    # restrict neighbourhood superset
    for (x in pcs) {

      dsep.pool = setdiff(c(pcs, unique(unlist(rsps))), x)

      # if k-degree filtering cannot be done any more, stop
      if(k > length(dsep.pool))
        break

      # try to d-separate neighbour X by conditioning with subsets of size k
      first.dsep = twoneighbourhood.first.dsep(x = t, y = x, z = c(),
            sz = dsep.pool, kmin = k, kmax = k, data = data, test = test,
            alpha = alpha, B = B, debug = debug)

      if (!is.null(first.dsep$pval) && first.dsep$pval > alpha) {

        # remove neighbour
        pcs = setdiff(pcs, x)
        pcs.max.pval = pcs.max.pval[pcs]

        # remove spouses by this neighbour
        rsps[[x]] = NULL

        # keep trace of the d-separator set
        dsep[[x]] = first.dsep$dsep

        if (x == n)
          return(list(
                is.neighbour = FALSE,
                max.pval = a,
                dsep = dsep[[x]]))

        # check if old neighbour could be a spouse
        for(y in setdiff(pcs, dsep[[x]])) {

          # is X a spouse of T by Y ?
          a = conditional.test(t, x, c(dsep[[x]], y), data = data, test = test, B = B, alpha = alpha, debug = debug)
          if (a <= alpha)
            twoneighbourhood.add.spouse(t, x, y, rsps[[y]], dsep, k, data, test, B, alpha, debug)

        }#FOR

        break

      }#THEN
      else {

        pcs.max.pval[x] = max(pcs.max.pval[x], a)

      }#ELSE

    }#FOR

    k = k + 1

  }#WHILE

  res = list(
        is.neighbour = TRUE,
        max.pval = pcs.max.pval[n],
        dsep = NULL)

  return(res)

}#TWONEIGHBOURHOOD.REVERSE.PCS.RSPS

twoneighbourhood.add.spouse = function(t, x, y, rspsy, dsep, kmax, data, test, B, alpha, debug) {

  rspsy = c(rspsy, x)

  if (kmax < 2)
    return(rspsy)

  # try to d-separate spouse X by conditioning with subsets of sizes 2 to kmax
  # (actually subsets of sizes 1 to kmax-1, to which we add Y)
  first.dsep = twoneighbourhood.first.dsep(x = x, y = t, z = c(dsep[[x]], y),
        sz = setdiff(rspsy, c(dsep[[x]], x)), kmin = 1, kmax = kmax - 1,
        data = data, test = test, alpha = alpha, B = B, debug = debug)

  if (!is.null(first.dsep$pval) && first.dsep$pval > alpha)
    rspsy = setdiff(rspsy, x)

  # if X could not have been d-separated, we then have to try to d-separate the
  # other spouses with subsets containing X
  if (x %in% rspsy) {
    for (sp in setdiff(rspsy, x)) {

      # avoid irrelevant tests, if X is already in SP's d-separating set
      if(x %in% dsep)
        break

      # try to d-separate spouse SP by conditioning with subsets of sizes 2 to
      # kmax containing X
      # (actually subsets of sizes 0 to kmax-2, to which we add X and Y)
      first.dsep = twoneighbourhood.first.dsep(x = sp, y = t, z = c(dsep[[sp]], y, x),
            sz = setdiff(rspsy, c(x, dsep[[sp]])), kmin = 0, kmax = kmax - 2,
            data = data, test = test, alpha = alpha, B = B, debug = debug)

      if (!is.null(first.dsep$pval) && first.dsep$pval > alpha)
        rspsy = setdiff(rspsy, sp)

    }#FOR
  }#THEN

  return(rspsy)

}#TWONEIGHBOURHOOD.ADD.SPOUSE

twoneighbourhood.first.dsep = function(x, y, z, sz, kmin, kmax, data, test, alpha,
  B, debug = FALSE) {

  max.pval = NULL
  max.dsep = NULL

  dsep.pool = setdiff(sz, c(x, y, z))

  for (k in kmin:kmax) {

    # if k-degree filtering cannot be done any more, stop
    if(k > length(dsep.pool))
      break

    # create all the possible subsets of size k from the current conditioning
    # superset
    dsep.subsets = subsets(length(dsep.pool), k, dsep.pool)

    # test independence with each subset
    for (s in 1:nrow(dsep.subsets)) {

      a = conditional.test(x, y, c(z, dsep.subsets[s,]), data = data, test = test, B = B, alpha = alpha, debug = debug)

      if(is.null(max.pval) || a > max.pval) {
        max.pval = a
        max.dsep = c(z, dsep.subsets[s,])
      }#THEN

      # if the p-value is already this high, it's useless to do further
      # testing (as it max.pval can only increase in value).
      if (max.pval > alpha)
        break

    }#FOR

    if (max.pval > alpha)
      break

  }#FOR

  return(list(
    dsep = max.dsep,
    pval = max.pval))

}#TWONEIGHBOURHOOD.FIRST.DSEP

get.pcs.rsps = function(t, data, nodes, whitelist, blacklist, test, alpha, B,
  backtracking = NULL, debug = FALSE) {

  pcs = vector()
  pcs.max.pval = vector()
  rsps = list()
  dsep = list()

  # Step I - 0 degree filtering
  #   build neighbourhood superset

  if(debug) {
    cat("----------------------------------------------------------------\n")
    cat("* 0 degree filtering\n")
  }#THEN

  for (x in setdiff(nodes, t)) {

     # is X a neighbour of T ?
    a = conditional.test(t, x, c(), data = data, test = test, B = B, alpha = alpha, debug = debug)
    if (a <= alpha) {

      if (debug)
        cat("  >", t ,"and", x, "are now neighbours\n")

      # add new neighbour
      pcs = c(pcs, x)
      pcs.max.pval[x] = a

    }#THEN
    else {

      # keep trace of the d-separator set
      dsep[[x]] = vector()

    }#ELSE

  }#FOR

  if (debug)
    cat("  >", t, "parents and children superset = '", pcs, "'\n")

  # Step II - 1 degree filtering
  #   restrict neighbourhood superset
  #   build spouses superset

  if(debug) {
    cat("* 1 degree filtering\n")
  }#THEN

  # heuristic : order neighbours from lower to higher correlated
  # this way we are more prone to remove less correlated nodes first
  ord = order(pcs.max.pval, decreasing = TRUE)
  pcs = pcs[ord]
  pcs.max.pval = pcs.max.pval[ord]

  # restrict neighbourhood superset
  for (x in pcs) {
    for(y in setdiff(pcs, x)) {

      # is X still a neighbour of T ?
      a = conditional.test(t, x, y, data = data, test = test, B = B, alpha = alpha, debug = debug)
      if (a > alpha) {

        if (debug)
          cat("  >", t ,"and", x, "are not neighbours any more\n")

        # remove neighbour
        pcs = setdiff(pcs, x)
        pcs.max.pval = pcs.max.pval[pcs]

        # keep trace of the d-separator set
        dsep[[x]] = y

        break

      }#THEN
      else {

        pcs.max.pval[x] = max(pcs.max.pval[x], a)

      }#ELSE

    }#FOR
  }#FOR

  # build spouses superset
  for (x in names(dsep)) {
    for(y in setdiff(pcs, dsep[[x]])) {

      # is X a spouse of T by Y ?
      a = conditional.test(t, x, c(dsep[[x]], y), data = data, test = test, B = B, alpha = alpha, debug = debug)
      if (a <= alpha) {

        if (debug)
          cat("  >", t ,"and", x, "are now spouses by", y, "\n")

        # add spouse by Y
        rsps[[y]] = c(rsps[[y]], x)

      }#THEN

    }#FOR
  }#FOR

  if (debug) {
    cat("  >", t, "parents and children superset = '", pcs, "'\n")
    for (y in names(rsps))
      cat("  >", t, "remaining spouses superset by", y, "= '", rsps[[y]], "'\n")
  }#THEN

  # Step III - k degree filtering
  #   restrict neighbourhood superset
  #   check if old neighbours could be spouses
  #   restrict spouses superset

  k = 2
  while (k <= length(pcs) + length(unique(unlist(rsps))) - 1) {

    if(debug) {
      cat("*", k, "degree filtering\n")
    }#THEN

    # heuristic : order neighbours from lower to higher correlated
    # this way we are more prone to remove less correlated nodes first
    ord = order(pcs.max.pval, decreasing = TRUE)
    pcs = pcs[ord]
    pcs.max.pval = pcs.max.pval[ord]

    # restrict spouses superset
    for (y in names(rsps)) {
      for (x in rsps[[y]]) {

        dsep.pool = setdiff(rsps[[y]], c(dsep[[x]], x))

        # if k-degree filtering cannot be done any more, stop
        if(k - 1 > length(dsep.pool))
          break

        # try to d-separate spouse X by conditioning with subsets of size k
        # (actually subsets of sizes k-1, to which we add Y)
        first.dsep = twoneighbourhood.first.dsep(x = t, y = x,
              z = c(dsep[[x]], y), sz = dsep.pool, kmin = k - 1, kmax = k - 1,
              data = data, test = test, alpha = alpha, B = B, debug = debug)

        if (!is.null(first.dsep$pval) && first.dsep$pval > alpha) {

          if (debug)
            cat("  >", t ,"and", x, "are not spouses by", y, "any more\n")

          # remove spouse by y
          rsps[[y]] = setdiff(rsps[[y]], x)

          break

        }#THEN

      }#FOR
    }#FOR

    # restrict neighbourhood superset
    for (x in pcs) {

      dsep.pool = setdiff(c(pcs, unique(unlist(rsps))), x)

      # if k-degree filtering cannot be done any more, stop
      if(k > length(dsep.pool))
        break

      # try to d-separate neighbour X by conditioning with subsets of size k
      first.dsep = twoneighbourhood.first.dsep(x = t, y = x,
            z = NULL, sz = dsep.pool, kmin = k, kmax = k, data = data,
            test = test, alpha = alpha, B = B, debug = debug)

      if (!is.null(first.dsep$pval) && first.dsep$pval > alpha) {

        if (debug)
          cat("  >", t ,"and", x, "are not neighbours any more\n")

        # remove neighbour
        pcs = setdiff(pcs, x)
        pcs.max.pval = pcs.max.pval[pcs]

        # remove spouses by this neighbour
        rsps[[x]] = NULL

        # keep trace of the d-separator set
        dsep[[x]] = first.dsep$dsep

        # check if old neighbours could be spouses
        for(y in setdiff(pcs, dsep[[x]])) {

          # is X a spouse of T by Y ?
          a = conditional.test(t, x, c(dsep[[x]], y), data = data, test = test, B = B, alpha = alpha, debug = debug)
          if (a <= alpha) {

            oldrsps = rsps[[y]]
            twoneighbourhood.add.spouse(t, x, y, rsps[[y]], dsep, k, data, test, B, alpha, debug)
            if (debug) {
              if (x %in% rsps[[y]])
                cat("  >", t ,"and", x, "are now spouses by", y, "\n")
              for (sp in setdiff(oldrsps, rsps[[y]]))
                cat("  >", t ,"and", sp, "are not spouses by", y, "any more\n")
            }#THEN

          }#THEN

        }#FOR

        break

      }#THEN
      else if (!is.null(first.dsep$pval)) {

        pcs.max.pval[x] = max(pcs.max.pval[x], a)

      }#THEN

    }#FOR

    if (debug) {
      cat("  >", t, "parents and children superset = '", pcs, "'\n")
      for (y in names(rsps))
        cat("  >", t, "remaining spouses superset by", y, "= '", rsps[[y]], "'\n")
    }#THEN

    k = k + 1

  }#WHILE

  res = list(
    nbr = pcs,
    mb = c(pcs, unique(unlist(rsps))))

  return(res)

}#GET.PCS.RSPS
