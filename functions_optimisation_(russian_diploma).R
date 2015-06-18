# Функция для мультипликативно сопряженного транспонирования матриц.
conjInv <- function(x, inv = maxplusinv, zero = -Inf) {
  res <- matrix(zero, nrow(x), ncol(x))
  res[x != zero] = inv(x[x != zero])
  t(res)
}

# Функция перемножения матриц.
multiply <- function(A, B, plus = max, mult = add) {
  if (ncol(A) != nrow(B))
    stop("Incompatible matrices!")
  rows <- nrow(A)
  cols <- ncol(B)
  res <- matrix(0., nrow = rows, ncol = cols)
  for (i in 1:rows) {
    for (j in 1:cols) {
      res[i,j] <- plus(mult(A[i,], B[,j]))
    }
  }
  res
}

# Функция сложения матриц. Используется, если сложение матриц не задано явно.
parplus <- function (..., plus = max, na.rm = FALSE)
{
  elts <- list(...)
  if (length(elts) == 0L)
    stop("no arguments")
  mmm <- elts[[1L]]
  attr(mmm, "dim") <- NULL
  has.na <- FALSE
  for (each in elts[-1L]) {
    attr(each, "dim") <- NULL
    l1 <- length(each)
    l2 <- length(mmm)
    if (l2 < l1) {
      if (l2 && l1%%l2)
        warning("an argument will be fractionally recycled")
      mmm <- rep(mmm, length.out = l1)
    }
    else if (l1 && l1 < l2) {
      if (l2%%l1)
        warning("an argument will be fractionally recycled")
      each <- rep(each, length.out = l2)
    }
    nas <- cbind(is.na(mmm), is.na(each))
    if (has.na || (has.na <- any(nas))) {
      mmm[nas[, 1L]] <- each[nas[, 1L]]
      each[nas[, 2L]] <- mmm[nas[, 2L]]
    }
    len <- length(mmm)
    for (i in 1:len) {
      mmm[i] <- plus(mmm[i], each[i])
    }
    if (has.na && !na.rm)
      mmm[nas[, 1L] | nas[, 2L]] <- NA
  }
  mostattributes(mmm) <- attributes(elts[[1L]])
  mmm
}

# Оператор <<Звезда Клини>>.
ast <- function(A, plus = max, mult = add, zero = -Inf, identity = 0,
                pplus = NULL) {
  d <- ncol(A)
  if (d != nrow(A))
    stop("Non-square matrix is given!")
  id <- matrix(zero, d, d, byrow=TRUE)
  if (d > 1)
    diag(id) <- identity
  else id <- identity
  res <- id
  temp <- A
  if (is.null(pplus))
    pplus <- function(...) parplus(..., plus=plus)
  res <- pplus(res, temp)
  if (d > 2) {
    for (i in 1:(d-2)) {
      temp <- multiply(temp, A, plus, mult)
      res <- pplus(res, temp)
    }
  }
  res
}

# Функция вычисления следа матрицы.
tr <- function(A, plus = max) {
  d <- ncol(A)
  if (d != nrow(A))
    stop("Non-square matrix is given!")
  if (d > 1)
    temp <- plus(diag(A))
  else
    temp <- A[1,1]
  temp
}

# Функция вычисления тропического аналога определителя.
Tr <- function(A, plus = max, mult = add) {
  d <- ncol(A)
  if (d != nrow(A))
    warning("Non-square matrix is given!")
  temp <- A
  res <- tr(A, plus)
  for (i in 2:d) {
    temp <- multiply(temp, A, plus, mult)
    res <- plus(res, tr(temp))
  }
  res
}

# Функция вычисления спектрального радиуса матрицы.
spectr <- function(A, plus = max, mult = add, deg = div) {
  d <- ncol(A)
  if (d != nrow(A))
    warning("Non-square matrix is given!")
  temp <- A
  res <- tr(A)
  for (i in 1:(d-1)) {
    temp <- multiply(temp, A, plus, mult)
    res <- plus(res, deg(tr(temp, plus), 1/(i+1)))
  }
  res
}

# Функция, решающая задачу без ограничений.
unconstr <- function(A, p, q, r, plus = max, mult = add, zero = -Inf,
                     identity = 0, pplus = NULL, deg = div,
                     inv = maxplusinv) {
  lambda <- spectr(A, plus, mult, deg)
  if (lambda == zero)
    stop("Incorrect matrix: eigenvalue equals zero!")
  myu <- plus(lambda, r)
  qm <- conjInv(q, inv = inv, zero=zero)
  d <- nrow(A)
  temp <- matrix(zero, d, d, byrow=TRUE)
  diag(temp) <- identity
  for (i in 1:d) {
    myu <- plus(myu, deg(multiply(multiply(qm, temp, plus, mult),
                                  p, plus, mult), 1/(i + 1)))
    temp <- multiply(temp, A, plus, mult)
  }
  myuminus <- inv(myu)
  matr <- ast(mult(myuminus, A), plus, mult, zero, identity, pplus)
  left <- mult(myuminus, p)
  right <- mult(myu, conjInv(multiply(qm, matr, plus, mult),
                             inv = inv, zero = zero))
  list(myu = myu, matr = matr, left = left, right = right, A = A,
       p = p, q = q, r = r)
}

# Функция, вычисляющая S_{km}
sCreate <- function(A, B, plus = max, mult = add, zero = -Inf,
                    identity = 0, pplus = NULL) {
  n <- nrow(A)
  # Массивы, используемые для вычисления M_{km}. Переиспользуются.
  mArr <- array(zero, c(n, n, n + 1))
  mNew <- array(zero, c(n, n, n + 1))
  # Массив, отвечающий за S_{k,n-1} после завершения работы функции.
  # В процессе работы в нем хранятся S_{km} предыдущих слоев.
  sArr <- array(zero, c(n, n, n + 1))
  # Массив, отвечающий за S_{kn}.
  snArr <- array(zero, c(n, n, n + 1))
  # Необходимо добавить единичную матрицу M_{00}.
  diag(sArr[,,1]) <- identity
  mArr[,,1] <- B
  mArr[,,2] <- A
  if (is.null(pplus))
    pplus <- function(...) parplus(..., plus=plus)
  for (i in 2:n) {
    for (j in 1:(i + 1))
      sArr[,,j] <- pplus(sArr[,,j], mNew[,,j])
    # Вычисляем следующий слой M_{km}.
    mNew[,,1] <- multiply(B, mArr[,,1], plus, mult)
    mNew[,,i + 1] <- multiply(A, mArr[,,i], plus, mult)
    for (j in 2:i)
      mNew[,,j] <- pplus(multiply(A, mArr[,,j - 1], plus, mult),
                         multiply(B, mArr[,,j]))
    mArr <- mNew
  }
  snArr <- pplus(sArr, mNew)
  list(sArr = sArr[,,1:n], snArr = snArr, A = A, B = B)
}

# Функция, решающая задачу с ограничениями.
constr <- function(A, p, q, r, B, plus = max, mult = add, zero = -Inf,
                   identity = 0, pplus = pmax, deg = div,
                   inv = maxplusinv) {
  lambda <- spectr(A, plus, mult, deg)
  if (lambda == zero)
    stop("Incorrect matrix: eigenvalue equals zero!")
  # Проверяем, что Tr(B) \\leq \\mathbb{1}.
  # Пользуемся тем, что x \\leq y <=> x \\oplus y = y.
  trB <- Tr(B, plus, mult)
  if ((trB != identity) && (plus(trB, identity) == trB))
    stop("Incorrect matrix: Tr(B) > \\mathbb{1}")
  n <- nrow(A)
  temp <- sCreate(A, B, plus, mult, zero, identity, pplus)
  myu <- r
  for (i in 1:n) {
    myu <- plus(myu, deg(tr(temp$snArr[,,i+1], plus), 1/i),
                deg(multiply(multiply(conjInv(q, inv=inv, zero=zero),
                                      temp$sArr[,,i], plus, mult),
                             p, plus, mult), 1/(i + 1)))
  }
  myuminus <- inv(myu)
  if (is.null(pplus))
    pplus <- function(...) parplus(..., plus=plus)
  matr <- ast(pplus(mult(myuminus, A), B), plus, mult, zero, identity)
  qm <- conjInv(q, inv = inv, zero = zero)
  left <- mult(myuminus, p)
  right <- mult(myu, conjInv(multiply(qm, matr, plus, mult),
                             inv = inv, zero = zero))
  xleft <- multiply(matr, left, plus, mult)
  xright <- multiply(matr, right, plus, mult)
  list(myu = myu, matr = matr, left = left, right = right, A = A,
       p = p, q = q, r = r, B = B, xleft = xleft, xright = xright)
}

# Функция умножения чисел в полуполе R_{max,+}.
add <- function(x, y) x + y

# Функция возведения в степень в полуполе R_{max,+}.
div <- function(x, m) x * m

# Функция взятия обратного в полуполе R_{max,+}.
maxplusinv <- function(x) -x