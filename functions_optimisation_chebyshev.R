maxplusless <- function(x, y) x < y

minimumFinder <- function(A, p, q, plus=max, mult=add, deg=div, zero=-Inf, 
                          identity=0, inv=maxplusinv, pplus=pmax) {  
  delta <- deg(multiply(conjInv(multiply(A, q, plus, mult), inv, zero),
                        p, plus, mult), 1/2)
  delta[1,1]
}


sparsify <- function(A, p, q, plus=max, mult=add, deg=div, zero=-Inf, 
                     identity=0, inv=maxplusinv, pplus=pmax, less=maxplusless) {
  delta <- minimumFinder(A, p, q, plus, mult, deg, zero, identity, inv, pplus)
  n <- ncol(A)
  As <- A
  delta2 <- inv(mult(delta, delta))
  
  for (i in 1:n) {
    for (j in 1:n) {
      if (maxplusless(A[i, j], mult(delta2, mult(p[i], inv(q[j]))))) {
        As[i, j] = zero
      }      
    }
  }  
  As
}

pmodify <- function(A, p, mult=add, inv=maxplusinv) {
  n <- ncol(A)
  k <- ncol(A)
  mA <- matrix(NA, n, n)
  for (i in 1:k) {
    for (j in 1:n) {
      mA[i,j] <- mult(A[i,j], inv(p[i,1]))
    }
  }
  mA
}

ordering <- function(A, plus=max, zero=-Inf) {
  n <- ncol(A)
  k <- nrow(A)
  fixA <- A
  ord <- matrix(rep(1:k, times=n), k, n)
  tempord <- matrix(rep(1:k, times=n), k, n)
  for (j in 1:n) {
    for (i in 1:(k-1)) {
      for (m in 1:(k-i)) {
        if (plus(A[m,j], A[m+1,j]) == A[m,j]) {
          tV <- A[m+1,j]
          tN <- ord[m+1,j]
          A[m+1,j] <- A[m,j]
          ord[m+1, j] <- ord[m,j]
          A[m,j] <- tV
          ord[m,j] <- tN
        }
      }
    }
    tempord[,j] <- ord[,j]
  }
  
  res <- matrix(NA, k, n)
  for (j in 1:n) {
    res[tempord[,j],j] <- 1:k
    for (m in 1:(k-1)) {      
      if (plus(A[m,j], A[m+1,j]) == A[m,j]) {
        res[ord[m,j],j] <- max(res[ord[m,j],j], res[ord[m+1,j],j])
        res[ord[m+1,j],j] <- res[ord[m,j],j]
      }      
    }
    for (m in (k-1):1) {      
      if (plus(A[m,j], A[m+1,j]) == A[m,j]) {
        res[ord[m,j],j] <- max(res[ord[m,j],j], res[ord[m+1,j],j])
        res[ord[m+1,j],j] <- res[ord[m,j],j]
      }      
    }
  }
  res <- res - 1
  res <- n-1 - res
  res[fixA==zero] <- n  
  res
}

filterPoints <- function(cur, pplus=pmax) {
  if (is.null(dim(cur)) || is.na(dim(cur)[2])) {
    if (is.null(cur)) warning("Ooops, cur is NULL")
    dim(cur) <- c(length(cur), 1)
  }
  k <- ncol(cur)
  toAdd <- matrix(TRUE, k, 1)
  res <- NULL
  if (k > 1) {
    for (i in 1:(k-1)) {
      if(toAdd[i,1]) {
        for (j in (i+1):k) {
          if(toAdd[j,]) {
            temp <- pplus(cur[,i], cur[,j])
            
            if (all(temp == cur[,i])) {
              toAdd[i,1] <- FALSE
              break
            }
            if (all(temp == cur[,j])) {
              toAdd[j,1] <- FALSE        
            }      
            
          }
        }
      }
    }
    res <- cur[,toAdd[,1]]
  }
  else {
    res <- cur[,1]
  }
  res
}

maxRow <- function(ordMatr, numbers) {
  num <- length(numbers)
  n <- ncol(ordMatr)
  maxNum <- 1
  maxValue <- -Inf
  if (num < 2) {
    maxNum <- numbers[[1]]
  }
  else {
    for (i in 1:num) {
      temp <- sum(ordMatr[numbers[[i]],], na.rm=T) - n/2 * sum(
        ordMatr[numbers[[i]],]==n)
      if (temp > maxValue) {
        maxValue <- temp
        maxNum <- numbers[[i]]
      }
    }
  }
  maxNum
}

nextmatr <- function(A, p, q, prev=NULL, selected=NULL, sorted=NULL,  
                     plus=max, mult=add, deg=div, 
                     zero=-Inf, identity=0, inv=maxplusinv,
                     pplus=pmax, less=maxplusless,
                     ordering=ordmin, maxRow=maxRowN, decreasing=T) {
  maxVariants <- 1
  n <- ncol(A)
  quantity <- 0
  fut <- 1:n
  if (!is.null(prev)) {
    fut <- fut[-prev]
  }
  else {
    A <- sparsify(A, p, q, plus, mult, deg, zero, identity, inv,
                     pplus, less)
    for (i in 1:n) {
      rowVariants <- sum(A[i,] != zero)
      if (rowVariants > 0) {
        maxVariants <- maxVariants * rowVariants
      }
    }
    # Cheking zero entries in p, any nonzero entry from A can be taken
    # on such places as they will be multiplicated by zero
    pnull <- which(p == zero)
    if (length(pnull) > 0) {
      prev <- c(prev, pnull)
      for (i in pnull) {
        selected <- c(selected, which(A[pnull,] != zero)[[1]])
      }
      fut <- fut[-pnull]
    }
    sorted <- ordering(pmodify(A, p, mult, inv), plus, zero)
  }
  
  ll <- NULL

  
  if (length(fut) > 1) {
    best <- maxRow(sorted, fut)
    if (best < 1) print("Error, best < 1")
    if (best > n) print("Error, best > n")
    for (j in 1:n) {
      if (A[best,j] != zero) {
        if (decreasing) {
          toFix <- which((sorted[fut,j] >= sorted[best, j])&(A[fut,j] != zero))
        }
        else {
          toFix <- which((sorted[fut,j] <= sorted[best, j])&(A[fut,j] != zero))
        }
        toDel <- fut[toFix]
        count <- length(toFix)
        toStay <- fut[-toFix]
        if (length(toStay > 0)) {
          res <- nextmatr(
            A, p, q, c(prev,toDel), c(selected, rep(j, count)), sorted,
            plus, mult, deg, zero, identity, inv, pplus, less,
            ordering, maxRow, decreasing
            )
          ll <- cbind(ll, res[[1]])
          quantity <- quantity + res[[2]]
        }
        else
        {
          toMult <- matrix(zero, n, n)
          bindedList <- cbind(c(prev,toDel), c(selected, rep(j, count)))
          toMult[bindedList] <- A[bindedList]
          delta = minimumFinder(A, p, q, plus, mult, deg, 
                                zero, identity, inv, pplus)
          ll <- cbind(ll, mult(inv(delta), multiply(conjInv(toMult, inv, zero),
                                                    p, plus, mult)))
          quantity <- quantity + 1
        }
      }
    }   
  }
  else { 
    # doesn't check length(fut)==0, can cause mistake
    num = sum(A[fut,] != zero)
    ret <- matrix(zero, n, num)
    counter = 1
    tempA <- matrix(zero, n, n)
    bindedList <- cbind(prev,selected)
    tempA[bindedList] <- A[bindedList]
    delta = minimumFinder(A, p, q, plus, mult, deg, 
                          zero, identity, inv, pplus)
    for (j in 1:n) {
      if (A[fut,j] != zero) {
        toMult <- tempA
        toMult[fut, j] <- A[fut, j]
        ret[,counter] <- mult(inv(delta), multiply(conjInv(toMult, inv, zero),
                                                   p, plus, mult))
        counter = counter + 1
      }      
    }  
    ll <- cbind(ll, ret)
    quantity <- num
  }  
  list(fp=filterPoints(ll), quant=quantity, variants=maxVariants)
}