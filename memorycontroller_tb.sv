// `include "interface.sv"
module memorycontroller_tb;

 mainbus bus();
 parameter ADDR_WIDTH = 7;
 parameter DATA_WIDTH = 8;

 // logic SCL,clk,reset_n;
 // logic SDA_OUT;
 logic [DATA_WIDTH-1:0]data_from_memory;
 // logic done;
 // logic [DATA_WIDTH-1:0]data_out;
 logic [ADDR_WIDTH-1:0] mem_addr;
 logic [DATA_WIDTH-1:0] data_to_memory;
 // logic mem_rw;
 // logic ack_n;
 
 
 task start;
	@(negedge bus.clk);
	// $display("%0t TB: Start task started", $time);
	bus.SCL = 1;
	bus.SDA_OUT = 1;
	// $display("%0t, TB_Start: SCL, SDA_OUT made 1, SCL=%0d, SDA_OUT=%0d",$time, SCL, SDA_OUT);
	@(negedge bus.clk);
	bus.SDA_OUT = 0;
	// $display("%0t, TB_Start: SDA_OUT made 0 for !SDA_OUT and end of TB_start, SDA_OUT=%0d",$time,SDA_OUT);
 endtask
 
 task stop;
	@(negedge bus.clk);
	// $display("%0t TB: StOP task started", $time);
	bus.SCL = 1;
	bus.SDA_OUT = 0;
	@(negedge bus.clk);
	// $display("%0t TB: StOP task started2", $time);
	bus.SDA_OUT = 1;
 endtask
 
 task sendaddr(input logic SDAA);
	@(negedge bus.clk);
		bus.SDA_OUT = SDAA;
 endtask
 
 task R_W(input logic R_W);
 @(negedge bus.clk);
 bus.SDA_OUT = R_W;
 endtask
 
 task senddata(input logic SDAD);
	@(negedge bus.clk);
		bus.SDA_OUT = SDAD;
 endtask
 
 task ack;
	@(negedge bus.clk);
	bus.SDA_OUT = 0;
 endtask
 
 task nack;
	@(negedge bus.clk);
	bus.SDA_OUT = 1;
 endtask
 
 
 
 task Applystimuluswrite(input logic[6:0] applyaddr, input logic[7:0] applydata, input logic readn_write);
	begin
	@(negedge bus.clk);
	bus.reset_n = 0;
	@(negedge bus.clk);
	 bus.reset_n = 1;
	
	start;
	
	sendaddr(applyaddr[0]);
	sendaddr(applyaddr[1]);
	sendaddr(applyaddr[2]);
	sendaddr(applyaddr[3]);
	sendaddr(applyaddr[4]);
	sendaddr(applyaddr[5]);
	sendaddr(applyaddr[6]);
	
	R_W(readn_write);
	
	@(posedge bus.clk);
	if(!bus.ack_n)
	begin
	@(negedge bus.clk);
	@(negedge bus.clk);
	senddata(applydata[0]);
	senddata(applydata[1]);
	senddata(applydata[2]);
	senddata(applydata[3]);
	senddata(applydata[4]);
	senddata(applydata[5]);
	senddata(applydata[6]);
	senddata(applydata[7]);
	end
	@(negedge bus.clk);
	if(!bus.ack_n)
		stop;
	@(negedge bus.clk);
	@(negedge bus.clk);
	end
 
 endtask
 
 task Applystimulusread(input logic[6:0] applyaddr, input logic readn_write);
	begin
	@(negedge bus.clk);
	bus.reset_n = 0;
	@(negedge bus.clk);
	 bus.reset_n = 1;
	
	start;
	
	sendaddr(applyaddr[0]);
	sendaddr(applyaddr[1]);
	sendaddr(applyaddr[2]);
	sendaddr(applyaddr[3]);
	sendaddr(applyaddr[4]);
	sendaddr(applyaddr[5]);
	sendaddr(applyaddr[6]);
	
	R_W(readn_write);
	

	@(posedge bus.clk);
	if(!bus.ack_n)
		stop;
	@(negedge bus.clk);
	@(negedge bus.clk);
	end
 
 endtask
 
 task FillMemory(input bit random);
 if(!random)
	begin
	$display("\n Filling with random Data");
	for(int i=0; i<(2**(ADDR_WIDTH)); i++)
		begin
		Applystimuluswrite(i,i,1);
		Applystimulusread(i,0);
		if(bus.data_out !== DUT.memory[i])
			$display("*** Error, Incorrect bus.data_out = %0d, Expected bus.data_out = %0d", bus.data_out, DUT.memory[i]);
		$display("bus.data_out = %0d", bus.data_out);
		end
	
		for(int i=0; i < (2**(ADDR_WIDTH)); i++)
			$display("memory[%0d] = %0d",i, DUT.memory[i]);
	end
else if(random)
	begin
	$display("\n Filling with random Data");
	for(int i=0; i<(2**(ADDR_WIDTH)); i++)
		begin
		Applystimuluswrite(i,$random,1);
		Applystimulusread(i,0);
		// Self-checking logic
		if(bus.data_out !== DUT.memory[i])
			$display("*** Error, Incorrect bus.data_out = %0d, Expected bus.data_out = %0d", bus.data_out, DUT.memory[i]);
		$display("bus.data_out = %0d", bus.data_out);
		end
	
	for(int i=0; i < (2**(ADDR_WIDTH)); i++)
			$display("memory[%0d] = %0d",i, DUT.memory[i]);
	end
 endtask


 memorycontroller DUT(.bus(bus.slave));

 initial
 begin
    bus.clk = 0;
	forever #5 bus.clk = ~bus.clk;
 end
 
 initial
 begin
	// Applystimuluswrite(127,30,1);
	// Applystimulusread(100,0);
	FillMemory(0); // Input data from 0 to 127
	FillMemory(1); // Fill with random data
	// $display("DUT.memory[100] = %0d", DUT.memory[100]);
	repeat(2)@(negedge bus.clk);
	$stop;
 end

endmodule

