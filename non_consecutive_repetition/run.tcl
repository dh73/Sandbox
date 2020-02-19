clear -all;
# Setup environment
# Read in HDL files
analyze -clear
analyze -sv12 /home/diego/sbx/repetitions/top.sv
elaborate -top top
clock i_clk
reset -expression !(i_rstn)
