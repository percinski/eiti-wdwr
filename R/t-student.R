library(MASS) # mvrnorm()
mu <- c(9, 8, 7, 6); # expected values 
sigma <- matrix(c(16,-2,-1,-3,-2,9,-4,-1,-1,-4,4,1,-3,-1,1,1), 4); # covariance matrix
nu <- 4; # degrees of freedom
n <- 10000; # number of scenarios
y <- t(t(mvrnorm(n, rep(0, length(mu)), sigma) * sqrt(nu / rchisq(n, nu))) + mu)

y <- y[y[,1]>=5,]
y <- y[y[,2]>=5,]
y <- y[y[,3]>=5,]
y <- y[y[,4]>=5,]
y <- y[y[,1]<=12,]
y <- y[y[,2]<=12,]
y <- y[y[,3]<=12,]
y <- y[y[,4]<=12,]
y <- y[1:1000,]

write.table(y, "scenarios.txt", sep=" ", eol="]\n[", row.names = FALSE, col.names=FALSE)
