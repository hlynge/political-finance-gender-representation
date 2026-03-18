# =============================================================================
# Political Finance, EMB Oversight, and Corruption
# Replication code
# =============================================================================
# Description:
#   Panel data analysis examining whether public financing of political parties
#   reduces corruption, and whether this effect is conditional on the capacity
#   and autonomy of electoral management bodies (EMBs).
#
# Data required (not included):
#   - V-Dem v15: V-Dem-CY-Full+Others-v15.csv
#     Source: https://v-dem.net/data/the-v-dem-dataset/
#   - IDEA political finance data (EMB oversight coding, manual)
#     Source: https://www.idea.int/data-tools/data/political-finance-database
#
# Place data files in a /data subdirectory before running.
# =============================================================================

rm(list = ls())

# -----------------------------------------------------------------------------
# 1. LIBRARIES
# -----------------------------------------------------------------------------

library(plm)
library(ggplot2)
library(lmtest)
library(stargazer)
library(sandwich)
library(stats)
library(hhi)
library(politicsR)
library(dplyr)
library(strucchange)
library(zoo)
library(data.table)
library(tseries)
library(car)

# -----------------------------------------------------------------------------
# 2. LOAD DATA
# -----------------------------------------------------------------------------

vdem <- read.csv("data/V-Dem-CY-Full+Others-v15.csv", header = TRUE, sep = ",")
nrow(vdem) # 27913

# Drop observations without COW code
vdem <- subset(vdem, !is.na(COWcode))
nrow(vdem) # 27068

# -----------------------------------------------------------------------------
# 3. CONSTRUCT VARIABLES
# -----------------------------------------------------------------------------

# --- 3a. IDEA EMB oversight dummies ---

# idea_broad: EMB responsible for party finance oversight in 2022
vdem["idea_broad"] <- 0
vdem$idea_broad[vdem$country_name %in% c(
  "Afghanistan", "Albania", "Angola", "Argentina", "Armenia", "Australia",
  "Azerbaijan", "Bangladesh", "Barbados", "Bhutan", "Bosnia and Herzegovina",
  "Botswana", "Brazil", "Cape Verde", "Cambodia", "Canada", "Chile",
  "Colombia", "Costa Rica", "Croatia", "Dominican Republic", "Ecuador",
  "Egypt", "Ethiopia", "Fiji", "Ghana", "Guinea-Bissau", "Guyana", "India",
  "Indonesia", "Kazakhstan", "Kenya", "South Korea", "Kyrgyzstan", "Lebanon",
  "Lesotho", "Liberia", "Libya", "Lithuania", "Malaysia", "Maldives", "Malta",
  "Mauritania", "Mexico", "Moldova", "Mozambique", "Burma/Myanmar", "Namibia",
  "Nepal", "New Zealand", "Nicaragua", "Nigeria", "Pakistan", "Panama",
  "Paraguay", "Peru", "Philippines", "Poland", "Romania", "Russia",
  "Seychelles", "Slovakia", "South Africa", "Sweden", "Tajikistan", "Thailand",
  "Timor-Leste", "Turkmenistan", "Uganda", "Ukraine", "United Kingdom",
  "United States of America", "Uruguay", "Venezuela"
)] <- 1

# idea_narrow: EMB responsible for oversight in both 2003 and 2022
vdem["idea_narrow"] <- 0
vdem$idea_narrow[vdem$country_name %in% c(
  "Armenia", "Australia", "Azerbaijan", "Bangladesh", "Bosnia and Herzegovina",
  "Brazil", "Cape Verde", "Canada", "Chile", "Colombia", "Costa Rica",
  "Dominican Republic", "Ecuador", "Ghana", "Guyana", "Lesotho", "Lithuania",
  "Mexico", "Moldova", "Mozambique", "New Zealand", "Nicaragua", "Panama",
  "Paraguay", "Peru", "Poland", "Russia", "South Africa", "Thailand",
  "Ukraine", "United Kingdom", "United States of America", "Venezuela"
)] <- 1

# --- 3b. EMB composite variables ---
vdem["capaut1"] <- vdem$v2elembcap + vdem$v2elembaut
vdem["capaut2"] <- (vdem$v2elembcap + vdem$v2elembaut) / 2

# --- 3c. Electoral system: majoritarian dummy ---
vdem["v2elparlel_maj"] <- NA
vdem$v2elparlel_maj[vdem$v2elparlel == 0] <- 1  # majoritarian
vdem$v2elparlel_maj[vdem$v2elparlel %in% c(1, 2, 3)] <- 0

# Carry forward within country
vdem <- vdem[order(vdem$COWcode, vdem$year), ]
vdem$v2elparlel_maj <- ave(
  vdem$v2elparlel_maj, vdem$COWcode,
  FUN = function(x) na.locf(x, na.rm = FALSE)
)

# --- 3d. Lagged variables (1–3 year lags) ---
vars_to_lag <- c(
  "v2x_corr", "v2x_execorr", "v2x_pubcorr", "v2xps_party",
  "v2psorgs", "v2psprlnks", "v2psplats", "v2pscohesv",
  "v2elpubfin", "v2elembcap", "v2elembaut", "capaut1",
  "capaut2", "v2cltrnslw"
)

vdem <- vdem %>%
  group_by(COWcode) %>%
  arrange(year) %>%
  mutate(
    across(
      all_of(vars_to_lag),
      list(
        l1 = ~ ifelse(year - lag(year, 1) == 1, lag(.x, 1), NA),
        l2 = ~ ifelse(year - lag(year, 2) == 2, lag(.x, 2), NA),
        l3 = ~ ifelse(year - lag(year, 3) == 3, lag(.x, 3), NA)
      ),
      .names = "{.col}_{.fn}"
    )
  ) %>%
  ungroup()

# -----------------------------------------------------------------------------
# 4. SUBSET AND ADDITIONAL VARIABLES
# -----------------------------------------------------------------------------

df <- subset(vdem, year >= 1960)
nrow(df) # 8514

# Election type dummies
df["eltype_leg"] <- 0
df$eltype_leg[df$v2eltype_0 == 1] <- 1

df["eltype_exe"] <- 0
df$eltype_exe[df$v2eltype_6 == 1] <- 1

# Legislative fractionalization (Herfindahl-based)
df["p1"] <- df$v2ellostsl / 100
df$p1[is.na(df$p1)] <- 0
df["p2"] <- df$v2ellostss / 100
df$p2[is.na(df$p2)] <- 0
df["p3"] <- df$v2ellostts / 100
df$p3[is.na(df$p3)] <- 0
df["p4"] <- 1 - (df$p1 + df$p2 + df$p3)
df$p4[is.na(df$p4)] <- 0

df["frac"] <- 1 - (df$p1^2 + df$p2^2 + df$p3^2 + df$p4^2)

# Carry forward fractionalization (max 3 periods)
df <- df[order(df$COWcode, df$year), ]

na.locf_max3 <- function(x, maxgap = 3) {
  n <- length(x)
  result <- x
  for (i in 2:n) {
    if (is.na(result[i])) {
      gap <- 0
      for (j in (i - 1):max(1, i - maxgap)) {
        gap <- gap + 1
        if (!is.na(result[j]) && gap <= maxgap) {
          result[i] <- result[j]
          break
        }
        if (!is.na(result[j])) break
      }
    }
  }
  return(result)
}

df$frac <- ave(df$frac, df$COWcode, FUN = function(x) na.locf_max3(x, maxgap = 3))

# -----------------------------------------------------------------------------
# 5. DIAGNOSTICS
# -----------------------------------------------------------------------------

df_sub <- subset(df, year >= 1974 & e_v2x_polyarchy_5C >= 0.25)

fixed <- plm(
  v2x_corr ~ v2elpubfin_l1 * v2elembcap_l1 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = df_sub, model = "within", index = c("COWcode", "year")
)

random <- plm(
  v2x_corr ~ v2elpubfin_l1 * v2elembcap_l1 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = df_sub, model = "random", random.method = "swar",
  index = c("COWcode", "year")
)

# Hausman test (FE vs RE)
hausman <- phtest(fixed, random)
cat("Hausman: χ² =", round(hausman$statistic, 2), ", p =", format.pval(hausman$p.value), "\n")

# Serial correlation
serial_bg <- pbgtest(fixed)
serial_w  <- pwartest(fixed)
cat("Serial correlation (BG): χ² =", round(serial_bg$statistic, 2), ", p =", format.pval(serial_bg$p.value), "\n")
cat("Serial correlation (W): F =",   round(serial_w$statistic, 2),  ", p =", format.pval(serial_w$p.value), "\n")

# Cross-sectional dependence
cd_test <- pcdtest(fixed, test = "cd")
cat("Cross-sectional dependence: z =", round(cd_test$statistic, 2), ", p =", format.pval(cd_test$p.value), "\n")

# Heteroskedasticity
bp_test <- bptest(fixed)
cat("Heteroskedasticity: χ² =", round(bp_test$statistic, 2), ", p =", format.pval(bp_test$p.value), "\n")

# Unit root tests
pdata <- pdata.frame(df_sub, index = c("COWcode", "year"))

tryCatch({
  purtest_dv <- purtest(v2x_corr ~ 1, data = pdata, test = "ips", lags = "AIC", pmax = 2)
  cat("Unit root (DV): p =", format.pval(purtest_dv$statistic$p.value), "\n")
}, error = function(e) cat("Unit root (DV): Test failed\n"))

tryCatch({
  purtest_iv <- purtest(v2elpubfin_l1 ~ 1, data = pdata, test = "ips", lags = "AIC", pmax = 2)
  cat("Unit root (IV): p =", format.pval(purtest_iv$statistic$p.value), "\n")
}, error = function(e) cat("Unit root (IV): Test failed\n"))

# VIF
m_pool <- lm(
  v2x_corr ~ v2elpubfin_l1 + v2elembcap_l1 + v2x_polyarchy +
    v2cacamps + frac + v2elparlel_maj + v2x_ex_direlect +
    log(e_gdppc) + log(e_pop),
  data = df_sub
)
vif_values <- vif(m_pool)
cat("Max VIF:", round(max(vif_values), 2), "\n")

# Influential observations
resids     <- residuals(fixed)
std_resid  <- scale(resids)[, 1]
n_inf      <- sum(abs(std_resid) > 3, na.rm = TRUE)
cat("Influential obs (|z| > 3):", n_inf, "(", round(100 * n_inf / length(resids), 2), "%)\n")

# Standard error comparison across four approaches
int_name <- grep("v2elpubfin_l1:v2elembcap_l1", names(coef(fixed)), value = TRUE)
int_coef <- coef(fixed)[int_name]

se_comparison <- data.frame(
  Specification = c("Naive", "Clustered", "Driscoll-Kraay", "Two-way"),
  Coefficient   = rep(int_coef, 4),
  SE = c(
    summary(fixed)$coef[int_name, "Std. Error"],
    coeftest(fixed, vcov = vcovHC(fixed, cluster = "group", type = "HC1"))[int_name, "Std. Error"],
    coeftest(fixed, vcov = vcovSCC(fixed, type = "HC3"))[int_name, "Std. Error"],
    coeftest(fixed, vcov = vcovDC(fixed))[int_name, "Std. Error"]
  )
)

se_comparison$t_stat  <- se_comparison$Coefficient / se_comparison$SE
se_comparison$p_value <- 2 * pt(-abs(se_comparison$t_stat),
                                 df = nobs(fixed) - length(coef(fixed)))
se_comparison$sig <- cut(
  se_comparison$p_value,
  breaks = c(0, 0.001, 0.01, 0.05, 0.1, 1),
  labels = c("***", "**", "*", "+", "")
)
print(se_comparison)

# -----------------------------------------------------------------------------
# 6. MAIN ANALYSIS (Table 1)
# -----------------------------------------------------------------------------
# Sample: 33 countries with EMB oversight responsibility in 2003 and 2022
# Period: 1989–2024; two-way FE; Driscoll-Kraay SEs

df_main <- subset(df, year >= 1989 & e_v2x_polyarchy_5C >= 0.0 & idea_narrow == 1)

m1 <- plm(
  v2x_corr ~ v2elpubfin_l1 + v2elembcap_l1 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = df_main, effect = "twoways", model = "within",
  index = c("COWcode", "year")
)

m2 <- plm(
  v2x_corr ~ v2elpubfin_l1 * v2elembcap_l1 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = df_main, effect = "twoways", model = "within",
  index = c("COWcode", "year")
)

m3 <- plm(
  v2x_execorr ~ v2elpubfin_l1 * v2elembcap_l1 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = df_main, effect = "twoways", model = "within",
  index = c("COWcode", "year")
)

m4 <- plm(
  v2x_pubcorr ~ v2elpubfin_l1 * v2elembcap_l1 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = df_main, effect = "twoways", model = "within",
  index = c("COWcode", "year")
)

r1 <- coeftest(m1, vcov = vcovSCC(m1, type = "HC3"))
r2 <- coeftest(m2, vcov = vcovSCC(m2, type = "HC3"))
r3 <- coeftest(m3, vcov = vcovSCC(m3, type = "HC3"))
r4 <- coeftest(m4, vcov = vcovSCC(m4, type = "HC3"))

# Text preview
stargazer(r1, r2, r3, r4, type = "text", style = "apsr",
          dep.var.labels = "", model.names = FALSE, digits = 3,
          star.cutoffs = c(0.1, 0.05, 0.01, 0.001),
          star.char = c("+", "*", "**", "***"))

# -----------------------------------------------------------------------------
# 7. MARGINAL EFFECTS PLOT (Figure 1)
# -----------------------------------------------------------------------------

df_sub <- subset(df, year >= 1989 & e_v2x_polyarchy_5C >= 0.0 & idea_narrow == 1)
coeffs <- m2$coefficients

median_controls <- c(
  median(df_sub$v2cacamps, na.rm = TRUE),
  median(df_sub$frac, na.rm = TRUE),
  median(df_sub$v2elparlel_maj, na.rm = TRUE),
  median(df_sub$v2x_ex_direlect, na.rm = TRUE),
  median(df_sub$v2mecenefm, na.rm = TRUE),
  median(df_sub$v2meharjrn, na.rm = TRUE),
  median(df_sub$e_v2xcs_ccsi_5C, na.rm = TRUE),
  median(df_sub$v2juhcind, na.rm = TRUE),
  median(log(df_sub$e_gdppc), na.rm = TRUE),
  median(log(df_sub$e_pop), na.rm = TRUE)
)

pubfin_range <- seq(-3, 4, by = 0.5)
embcap_10    <- quantile(df_sub$v2elembcap_l1, 0.1, na.rm = TRUE)
embcap_50    <- quantile(df_sub$v2elembcap_l1, 0.5, na.rm = TRUE)
embcap_90    <- quantile(df_sub$v2elembcap_l1, 0.9, na.rm = TRUE)

make_pred <- function(pubfin_range, embcap_val, label) {
  xhyp <- cbind(pubfin_range, embcap_val,
                matrix(median_controls, nrow = length(pubfin_range),
                       ncol = length(median_controls), byrow = TRUE),
                pubfin_range * embcap_val)
  data.frame(pubfin = pubfin_range, predicted = as.vector(xhyp %*% coeffs),
             embcap_level = label)
}

df_plot <- rbind(
  make_pred(pubfin_range, embcap_10, "Low (10th pct)"),
  make_pred(pubfin_range, embcap_50, "Medium (50th pct)"),
  make_pred(pubfin_range, embcap_90, "High (90th pct)")
)

df_plot$embcap_level <- factor(
  df_plot$embcap_level,
  levels = c("High (90th pct)", "Medium (50th pct)", "Low (10th pct)")
)

ggplot(df_plot, aes(x = pubfin, y = predicted,
                    color = embcap_level, linetype = embcap_level)) +
  geom_line(size = 1.2) +
  geom_rug(data = df_sub, aes(x = v2elpubfin_l1), inherit.aes = FALSE,
           sides = "b", alpha = 0.3, length = unit(0.02, "npc")) +
  labs(
    x = "Public Funding (t-1)",
    y = "Predicted Political Corruption\n(Within-Country Deviations, Higher = More Corrupt)",
    color = "EMB Capacity:", linetype = "EMB Capacity:"
  ) +
  theme_minimal(base_size = 12) +
  theme(legend.position = "bottom", legend.text = element_text(size = 10),
        panel.grid.minor = element_blank()) +
  scale_color_manual(values = c(
    "High (90th pct)"   = "#000000",
    "Medium (50th pct)" = "#666666",
    "Low (10th pct)"    = "#CCCCCC"
  )) +
  scale_linetype_manual(values = c(
    "High (90th pct)"   = "solid",
    "Medium (50th pct)" = "dashed",
    "Low (10th pct)"    = "dotted"
  ))

ggsave("figure1_marginal_effects.pdf", width = 7, height = 5)

# -----------------------------------------------------------------------------
# 8. ROBUSTNESS: ALTERNATIVE LAG STRUCTURES (Table A1)
# -----------------------------------------------------------------------------

m_l1 <- plm(
  v2x_corr ~ v2elpubfin_l1 * v2elembcap_l1 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = df_main, effect = "twoways", model = "within",
  index = c("COWcode", "year")
)
m_l2 <- plm(
  v2x_corr ~ v2elpubfin_l2 * v2elembcap_l2 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = df_main, effect = "twoways", model = "within",
  index = c("COWcode", "year")
)
m_l3 <- plm(
  v2x_corr ~ v2elpubfin_l3 * v2elembcap_l3 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = df_main, effect = "twoways", model = "within",
  index = c("COWcode", "year")
)

r_l1 <- coeftest(m_l1, vcov = vcovSCC(m_l1, type = "HC3"))
r_l2 <- coeftest(m_l2, vcov = vcovSCC(m_l2, type = "HC3"))
r_l3 <- coeftest(m_l3, vcov = vcovSCC(m_l3, type = "HC3"))

stargazer(r_l1, r_l2, r_l3, type = "text", style = "apsr",
          dep.var.labels = "", model.names = FALSE, digits = 3,
          star.cutoffs = c(0.1, 0.05, 0.01, 0.001),
          star.char = c("+", "*", "**", "***"))

stargazer(r_l1, r_l2, r_l3, type = "html", out = "tableA1.html",
          title = "Table A1: Alternative Lag Structure",
          style = "apsr",
          column.labels = c("t-1 lag", "t-2 lag", "t-3 lag"),
          dep.var.labels = "", model.names = FALSE,
          covariate.labels = c(
            "Public funding", "EMB capacity",
            "Political polarization", "Legislative fractionalization",
            "Majoritarian electoral system", "Direct executive election",
            "Media censorship efforts (reverse)",
            "Harassment of journalists (reverse)",
            "Civil society strength", "Judicial independence",
            "GDP per capita (log)", "Population (log)",
            "Public funding × EMB capacity"
          ),
          add.lines = list(
            c("Lag structure", "t-1", "t-2", "t-3"),
            c("Country FE", "Yes", "Yes", "Yes"),
            c("Year FE", "Yes", "Yes", "Yes"),
            c("Countries", "33", "33", "33"),
            c("Period", "1989-2024", "1989-2024", "1989-2024")
          ),
          digits = 3,
          star.cutoffs = c(0.1, 0.05, 0.01, 0.001),
          star.char = c("+", "*", "**", "***"),
          notes = c(
            "Driscoll-Kraay standard errors in parentheses.",
            "Sample: 33 countries where EMBs held oversight responsibility 2003 and 2022.",
            "+ p<0.1; * p<0.05; ** p<0.01; *** p<0.001"
          ),
          notes.append = FALSE, notes.align = "l",
          omit.stat = c("f", "ser"))

# -----------------------------------------------------------------------------
# 9. ROBUSTNESS: REGIME HETEROGENEITY (Table A2)
# -----------------------------------------------------------------------------

df_a2 <- subset(df, year >= 1989 & idea_narrow == 1)

m_reg1 <- plm(
  v2x_corr ~ v2elpubfin_l1 * v2elembcap_l1 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = subset(df_a2, e_v2x_polyarchy_5C >= 0.0),
  effect = "twoways", model = "within", index = c("COWcode", "year")
)
m_reg2 <- plm(
  v2x_corr ~ v2elpubfin_l1 * v2elembcap_l1 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = subset(df_a2, e_v2x_polyarchy_5C >= 0.25),
  effect = "twoways", model = "within", index = c("COWcode", "year")
)
m_reg3 <- plm(
  v2x_corr ~ v2elpubfin_l1 * v2elembcap_l1 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = subset(df_a2, e_v2x_polyarchy_5C >= 0.5),
  effect = "twoways", model = "within", index = c("COWcode", "year")
)

r_reg1 <- coeftest(m_reg1, vcov = vcovSCC(m_reg1, type = "HC3"))
r_reg2 <- coeftest(m_reg2, vcov = vcovSCC(m_reg2, type = "HC3"))
r_reg3 <- coeftest(m_reg3, vcov = vcovSCC(m_reg3, type = "HC3"))

n_countries_m1 <- length(unique(subset(df_a2, e_v2x_polyarchy_5C >= 0.00 &
                                         !is.na(v2x_corr) & !is.na(v2elpubfin_l1) &
                                         !is.na(v2elembcap_l1))$COWcode))
n_countries_m2 <- length(unique(subset(df_a2, e_v2x_polyarchy_5C >= 0.25 &
                                         !is.na(v2x_corr) & !is.na(v2elpubfin_l1) &
                                         !is.na(v2elembcap_l1))$COWcode))
n_countries_m3 <- length(unique(subset(df_a2, e_v2x_polyarchy_5C >= 0.50 &
                                         !is.na(v2x_corr) & !is.na(v2elpubfin_l1) &
                                         !is.na(v2elembcap_l1))$COWcode))

stargazer(r_reg1, r_reg2, r_reg3, type = "html", out = "tableA2.html",
          title = "Table A2: Regime Heterogeneity",
          style = "apsr",
          column.labels = c("All regimes", "Non-autocracies", "Democracies"),
          dep.var.labels = "", model.names = FALSE,
          covariate.labels = c(
            "Public funding (t-1)", "EMB capacity (t-1)",
            "Political polarization", "Legislative fractionalization",
            "Majoritarian electoral system", "Direct executive election",
            "Media censorship efforts (reverse)",
            "Harassment of journalists (reverse)",
            "Civil society strength", "Judicial independence",
            "GDP per capita (log)", "Population (log)",
            "Public funding × EMB capacity"
          ),
          add.lines = list(
            c("Regime cutoff", "≥0.0", "≥0.25", "≥0.5"),
            c("Regime type", "All", "Hybrid+Demo", "Democracy"),
            c("Country FE", "Yes", "Yes", "Yes"),
            c("Year FE", "Yes", "Yes", "Yes"),
            c("Countries",
              as.character(n_countries_m1),
              as.character(n_countries_m2),
              as.character(n_countries_m3)),
            c("Period", "1989-2024", "1989-2024", "1989-2024")
          ),
          digits = 3,
          star.cutoffs = c(0.1, 0.05, 0.01, 0.001),
          star.char = c("+", "*", "**", "***"),
          notes = c(
            "Driscoll-Kraay standard errors in parentheses.",
            "Sample: 33 countries where EMBs held oversight responsibility 2003 and 2022.",
            "+ p<0.1; * p<0.05; ** p<0.01; *** p<0.001"
          ),
          notes.append = FALSE, notes.align = "l",
          omit.stat = c("f", "ser"))

# -----------------------------------------------------------------------------
# 10. ROBUSTNESS: ALTERNATIVE OVERSIGHT MEASURES (Table A3)
# -----------------------------------------------------------------------------

df_a3 <- subset(df, year >= 1989 & e_v2x_polyarchy_5C >= 0.0 & idea_narrow == 1)

m_ov1 <- plm(
  v2x_corr ~ v2elpubfin_l1 * v2elembcap_l1 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = df_a3, effect = "twoways", model = "within",
  index = c("COWcode", "year")
)
m_ov2 <- plm(
  v2x_corr ~ v2elpubfin_l1 * v2elembaut_l1 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = df_a3, effect = "twoways", model = "within",
  index = c("COWcode", "year")
)
m_ov3 <- plm(
  v2x_corr ~ v2elpubfin_l1 * capaut2_l1 + v2cacamps + frac +
    v2elparlel_maj + v2x_ex_direlect + v2mecenefm + v2meharjrn +
    e_v2xcs_ccsi_5C + v2juhcind + log(e_gdppc) + log(e_pop),
  data = df_a3, effect = "twoways", model = "within",
  index = c("COWcode", "year")
)

r_ov1 <- coeftest(m_ov1, vcov = vcovSCC(m_ov1, type = "HC3"))
r_ov2 <- coeftest(m_ov2, vcov = vcovSCC(m_ov2, type = "HC3"))
r_ov3 <- coeftest(m_ov3, vcov = vcovSCC(m_ov3, type = "HC3"))

stargazer(r_ov1, r_ov2, r_ov3, type = "html", out = "tableA3.html",
          title = "Table A3: Alternative Oversight Measures",
          style = "apsr",
          column.labels = c("Capacity", "Autonomy", "Capacity+Autonomy"),
          dep.var.labels = "", model.names = FALSE,
          covariate.labels = c(
            "Public funding (t-1)", "EMB capacity (t-1)",
            "EMB autonomy (t-1)", "EMB capacity+autonomy (t-1)",
            "Political polarization", "Legislative fractionalization",
            "Majoritarian electoral system", "Direct executive election",
            "Media censorship efforts (reverse)",
            "Harassment of journalists (reverse)",
            "Civil society strength", "Judicial independence",
            "GDP per capita (log)", "Population (log)",
            "Public funding × EMB capacity",
            "Public funding × EMB autonomy",
            "Public funding × EMB cap+aut"
          ),
          add.lines = list(
            c("Oversight measure", "Capacity", "Autonomy", "Combined"),
            c("Country FE", "Yes", "Yes", "Yes"),
            c("Year FE", "Yes", "Yes", "Yes"),
            c("Countries", "33", "33", "33"),
            c("Period", "1989-2024", "1989-2024", "1989-2024")
          ),
          digits = 3,
          star.cutoffs = c(0.1, 0.05, 0.01, 0.001),
          star.char = c("+", "*", "**", "***"),
          notes = c(
            "Driscoll-Kraay standard errors in parentheses.",
            "Sample: 33 countries where EMBs held oversight responsibility 2003 and 2022.",
            "+ p<0.1; * p<0.05; ** p<0.01; *** p<0.001"
          ),
          notes.append = FALSE, notes.align = "l",
          omit.stat = c("f", "ser"))

# -----------------------------------------------------------------------------
# 11. COMPREHENSIVE SPECIFICATION ANALYSIS (Table A4)
# -----------------------------------------------------------------------------
# 729 specifications varying: DV (3) × oversight (3) × time (3) ×
# regime (3) × lag (3) × sample (3)

dependent_vars <- c("v2x_corr", "v2x_execorr", "v2x_pubcorr")
oversight_vars <- c("v2elembcap", "v2elembaut", "capaut2")
time_cuts      <- c(1960, 1974, 1989)
regime_cuts    <- c(0.0, 0.25, 0.5)
lag_periods    <- c(1, 2, 3)
sample_types   <- c("all", "idea_broad", "idea_narrow")

controls <- paste0(
  "v2cacamps + frac + v2elparlel_maj + v2x_ex_direlect + ",
  "v2mecenefm + v2meharjrn + e_v2xcs_ccsi_5C + v2juhcind + ",
  "log(e_gdppc) + log(e_pop)"
)

results_list <- list()
counter <- 1

for (dv in dependent_vars) {
  for (oversight in oversight_vars) {
    for (time_cut in time_cuts) {
      for (regime_cut in regime_cuts) {
        for (lag in lag_periods) {
          for (sample_type in sample_types) {

            lag_suffix <- paste0("_l", lag)

            df_sub <- switch(sample_type,
              all         = subset(df, year >= time_cut & e_v2x_polyarchy_5C >= regime_cut),
              idea_broad  = subset(df, year >= time_cut & e_v2x_polyarchy_5C >= regime_cut & idea_broad == 1),
              idea_narrow = subset(df, year >= time_cut & e_v2x_polyarchy_5C >= regime_cut & idea_narrow == 1)
            )

            formula_str <- paste0(
              dv, " ~ v2elpubfin", lag_suffix, " * ", oversight, lag_suffix,
              " + ", controls
            )

            model_result <- tryCatch({
              m <- plm(as.formula(formula_str), data = df_sub,
                       effect = "twoways", model = "within",
                       index = c("COWcode", "year"))
              m_robust <- coeftest(m, vcov = vcovSCC(m, type = "HC3"))

              pubfin_var      <- paste0("v2elpubfin", lag_suffix)
              oversight_var_n <- paste0(oversight, lag_suffix)
              interaction_var <- paste0("v2elpubfin", lag_suffix, ":", oversight, lag_suffix)

              list(
                spec_id        = counter,
                dependent_var  = dv,
                oversight_var  = oversight,
                time_start     = time_cut,
                regime_cutoff  = regime_cut,
                lag            = lag,
                sample_type    = sample_type,
                n_obs          = nobs(m),
                n_countries    = length(unique(df_sub$COWcode[!is.na(df_sub[[dv]])])),
                pubfin_coef    = m_robust[pubfin_var, "Estimate"],
                pubfin_se      = m_robust[pubfin_var, "Std. Error"],
                pubfin_pval    = m_robust[pubfin_var, "Pr(>|t|)"],
                oversight_coef = m_robust[oversight_var_n, "Estimate"],
                oversight_se   = m_robust[oversight_var_n, "Std. Error"],
                oversight_pval = m_robust[oversight_var_n, "Pr(>|t|)"],
                interaction_coef = m_robust[interaction_var, "Estimate"],
                interaction_se   = m_robust[interaction_var, "Std. Error"],
                interaction_pval = m_robust[interaction_var, "Pr(>|t|)"],
                r_squared_within = summary(m)$r.squared[1]
              )
            }, error = function(e) {
              list(spec_id = counter, dependent_var = dv, oversight_var = oversight,
                   time_start = time_cut, regime_cutoff = regime_cut, lag = lag,
                   sample_type = sample_type, error = as.character(e))
            })

            results_list[[counter]] <- model_result
            counter <- counter + 1

            if (counter %% 50 == 0) cat("Completed", counter, "specifications...\n")
          }
        }
      }
    }
  }
}

results_df <- bind_rows(lapply(results_list, function(x) x[!names(x) %in% c("model", "model_robust")]))

results_df <- results_df %>%
  mutate(
    interaction_sig = case_when(
      interaction_pval < 0.001 ~ "***",
      interaction_pval < 0.01  ~ "**",
      interaction_pval < 0.05  ~ "*",
      interaction_pval < 0.1   ~ "+",
      TRUE                     ~ ""
    ),
    interaction_negative = interaction_coef < 0,
    interaction_sig_neg  = interaction_sig %in% c("+", "*", "**", "***") & interaction_negative
  )

# Summary statistics across 729 specifications
cat("\n--- Specification Robustness Summary ---\n")
cat("Total specs:", nrow(results_df), "\n")
cat("Significant negative (p<0.05):",
    sum(results_df$interaction_pval < 0.05 & results_df$interaction_negative, na.rm = TRUE), "\n")
cat("Predicted negative sign:",
    sum(results_df$interaction_negative, na.rm = TRUE), "\n")

# -----------------------------------------------------------------------------
# 12. EVENT STUDY (Table A5, Figure A1)
# -----------------------------------------------------------------------------
# Tests for pre-trends (reverse causality) using leads and lags ±3 years

df_event <- df %>%
  group_by(COWcode) %>%
  arrange(year) %>%
  mutate(
    pubfin_lead3 = ifelse(year - lead(year, 3) == -3, lead(v2elpubfin, 3), NA),
    pubfin_lead2 = ifelse(year - lead(year, 2) == -2, lead(v2elpubfin, 2), NA),
    pubfin_lead1 = ifelse(year - lead(year, 1) == -1, lead(v2elpubfin, 1), NA),
    pubfin_lag1  = ifelse(year - lag(year, 1) == 1,   lag(v2elpubfin, 1), NA),
    pubfin_lag2  = ifelse(year - lag(year, 2) == 2,   lag(v2elpubfin, 2), NA),
    pubfin_lag3  = ifelse(year - lag(year, 3) == 3,   lag(v2elpubfin, 3), NA),
    embcap_lead3 = ifelse(year - lead(year, 3) == -3, lead(v2elembcap, 3), NA),
    embcap_lead2 = ifelse(year - lead(year, 2) == -2, lead(v2elembcap, 2), NA),
    embcap_lead1 = ifelse(year - lead(year, 1) == -1, lead(v2elembcap, 1), NA),
    embcap_lag1  = ifelse(year - lag(year, 1) == 1,   lag(v2elembcap, 1), NA),
    embcap_lag2  = ifelse(year - lag(year, 2) == 2,   lag(v2elembcap, 2), NA),
    embcap_lag3  = ifelse(year - lag(year, 3) == 3,   lag(v2elembcap, 3), NA)
  ) %>%
  ungroup()

df_event_main <- subset(df_event, year >= 1989 & e_v2x_polyarchy_5C >= 0.0 & idea_narrow == 1)

event_model <- plm(
  v2x_corr ~
    pubfin_lead3 + pubfin_lead2 + pubfin_lead1 +
    v2elpubfin + pubfin_lag1 + pubfin_lag2 + pubfin_lag3 +
    embcap_lead3 + embcap_lead2 + embcap_lead1 +
    v2elembcap + embcap_lag1 + embcap_lag2 + embcap_lag3 +
    pubfin_lead3:embcap_lead3 + pubfin_lead2:embcap_lead2 + pubfin_lead1:embcap_lead1 +
    v2elpubfin:v2elembcap +
    pubfin_lag1:embcap_lag1 + pubfin_lag2:embcap_lag2 + pubfin_lag3:embcap_lag3 +
    v2cacamps + frac + v2elparlel_maj + v2x_ex_direlect +
    v2mecenefm + v2meharjrn + e_v2xcs_ccsi_5C + v2juhcind +
    log(e_gdppc) + log(e_pop),
  data = df_event_main, effect = "twoways", model = "within",
  index = c("COWcode", "year")
)

event_results <- coeftest(event_model, vcov = vcovSCC(event_model, type = "HC3"))

interaction_terms <- c(
  "pubfin_lead3:embcap_lead3", "pubfin_lead2:embcap_lead2",
  "pubfin_lead1:embcap_lead1", "v2elpubfin:v2elembcap",
  "pubfin_lag1:embcap_lag1", "pubfin_lag2:embcap_lag2",
  "pubfin_lag3:embcap_lag3"
)

event_coefs <- data.frame(
  period = c(-3, -2, -1, 0, 1, 2, 3),
  coef   = event_results[interaction_terms, "Estimate"],
  se     = event_results[interaction_terms, "Std. Error"]
)

event_coefs$ci_lower   <- event_coefs$coef - 1.96 * event_coefs$se
event_coefs$ci_upper   <- event_coefs$coef + 1.96 * event_coefs$se
event_coefs$significant <- event_coefs$ci_lower * event_coefs$ci_upper > 0
print(event_coefs)

# Figure A1
ggplot(event_coefs, aes(x = period, y = coef)) +
  geom_point(size = 3, color = "black") +
  geom_errorbar(aes(ymin = ci_lower, ymax = ci_upper), width = 0.2, color = "black") +
  geom_hline(yintercept = 0, linetype = "dashed", color = "gray50") +
  geom_vline(xintercept = -0.5, linetype = "dotted", color = "gray70") +
  labs(
    x = "Years Relative to Current Period (t=0)",
    y = "Interaction Coefficient\n(Public Funding × EMB Capacity)"
  ) +
  theme_minimal(base_size = 12) +
  theme(panel.grid.minor = element_blank(),
        axis.title.x = element_text(margin = margin(t = 10)),
        axis.title.y = element_text(margin = margin(r = 10))) +
  scale_x_continuous(breaks = -3:3,
                     labels = c("t-3", "t-2", "t-1", "t=0", "t+1", "t+2", "t+3"))

ggsave("figureA1_event_study.pdf", width = 7, height = 5)

# Table A5
stargazer(event_results, type = "html", out = "tableA5.html",
          title = "Event Study: Dynamic Effects of Public Funding × EMB Capacity",
          style = "apsr",
          dep.var.labels = "", model.names = FALSE,
          keep = interaction_terms,
          covariate.labels = c(
            "t-3 (Lead 3)", "t-2 (Lead 2)", "t-1 (Lead 1)",
            "t=0 (Current)", "t+1 (Lag 1)", "t+2 (Lag 2)", "t+3 (Lag 3)"
          ),
          add.lines = list(
            c("Controls", "Yes"),
            c("Country FE", "Yes"),
            c("Year FE", "Yes"),
            c("Countries", "33"),
            c("Period", "1989-2024")
          ),
          digits = 3,
          star.cutoffs = c(0.1, 0.05, 0.01, 0.001),
          star.char = c("+", "*", "**", "***"),
          notes = c(
            "Driscoll-Kraay standard errors in parentheses.",
            "Sample: 33 countries where EMBs held oversight responsibility 2003 and 2022.",
            "Pre-treatment coefficients (t-3 to t-1) test for reverse causality.",
            "Post-treatment coefficients (t=0 to t+3) show dynamic effects.",
            "+ p<0.1; * p<0.05; ** p<0.01; *** p<0.001"
          ),
          notes.append = FALSE, notes.align = "l",
          omit.stat = c("f", "ser"))

# =============================================================================
# END OF SCRIPT
# =============================================================================
