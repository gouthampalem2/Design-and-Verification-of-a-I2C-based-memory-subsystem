vlib work
vdel -all
vlib work

vlog memorycontroller.sv
vlog memorycontroller_tb.sv +acc
vlog FunctionalUnit.sv
vlog FunctionalUnit_tb.sv +acc
vlog i2c.sv
vlog i2c_tb.sv
vlog top.sv
vlog tb.sv

#vsim work.memorycontroller_tb
#vsim work.i2c_tb
#vsim work.FunctionalUnitTest
vsim work.tb

#add wave -r *
#do wave.do
run -all