module tb;

mainbus bus();

parameter ADDR_WIDTH = 7;
parameter DATA_WIDTH = 8;

// bit bus.clk,bus.reset_n;
// logic [DATA_WIDTH-1:0] Data_In;
// logic [ADDR_WIDTH-1:0] Addr_In;
// logic [2:0] S;
// logic MSBIn;
// logic LSBIn;
// logic M_en;
// logic R_W;

// logic [DATA_WIDTH-1:0] bus.Data_Out;
// logic Done;

top t0();


always #5 bus.clk = ~bus.clk;

initial
begin

	@(negedge bus.clk);
	bus.reset_n = 0;
	
	@(negedge bus.clk);
	bus.reset_n = 1;
	
	@(negedge bus.clk);
	bus.M_en = 1;
	@(negedge bus.clk);
	bus.ADDR = 7'd120;
	bus.F_In = 7'd120;
	bus.R_W = 1;
	bus.S = 3'b000;
	bus.MSBIn = '1;
	bus.LSBIn = '0;
	
	// repeat(400) @(negedge bus.clk);
	// $display("bus.Data_Out = %0d", bus.data_out);
	// for(int i=0; i < (2**(ADDR_WIDTH)); i++)
			// $display("memory[%0d] = %0d",i, t0.M0.memory[i]);
	
	@(negedge bus.clk);
	$display("t0.M0.memory[100] = %0d", t0.M0.memory[100]);
	repeat(20) @(negedge bus.clk);
	$stop;
end

endmodule