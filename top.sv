interface mainbus;
parameter DATA_WIDTH = 8;
logic SCL;
logic SDA;
logic ack_n;
logic done;
logic [DATA_WIDTH-1:0]data_out, F_Out;
logic mem_rw;
bit clk,reset_n;

logic SDA_OUT;
logic data_ready, data_rdy;
logic M_EN;
logic [6:0] ADDR;
logic [7:0] DATA_IN;
logic R_W;
logic [DATA_WIDTH-1:0] Data_In, F_In;
logic [2:0] S;
logic MSBIn;
logic LSBIn;
logic M_en;


modport master (input clk,input reset_n,input ack_n,input ADDR, input F_Out, input M_EN, input data_rdy, input R_W, output SCL, output SDA_OUT);
modport slave (input clk,input reset_n,input SCL,input SDA_OUT, output ack_n, output done, output data_out);
modport functional_unit(output F_Out, output data_rdy, input clk, input reset_n, input F_In, input S, input MSBIn, input LSBIn, input M_en);


endinterface



module top;

parameter ADDR_WIDTH = 7;
parameter DATA_WIDTH = 8;

mainbus bus();
// inputs and outputs declaration
// input logic clk;
// input logic reset_n;
// input logic [DATA_WIDTH-1:0] Data_In;
// input logic [ADDR_WIDTH-1:0] Addr_In;
// input logic [2:0] S;
// input logic MSBIn;
// input logic LSBIn;
// input logic M_en;
// input logic R_W;

// output logic [DATA_WIDTH-1:0] Data_Out;
// output logic Done;

// logic [DATA_WIDTH-1:0] F_Out;
// logic data_rdy;
// logic SCA;

FunctionalUnit F0(bus.functional_unit);
i2c i0(bus.master);
memorycontroller M0(bus.slave);

endmodule