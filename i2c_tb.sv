module i2c_tb;

mainbus bus();
parameter DATA_WIDTH=8;
parameter ADDR_WIDTH=7;


logic [ADDR_WIDTH-1:0]temp_addr;
logic [DATA_WIDTH-1:0]temp_data ;
logic temp_scl;
logic temp_r_w;
logic data_rdy ='0;
logic scl_seq;

int count=0;
int temp_i=0;
int wait_counter;

 task resettask;
 begin
	@(negedge bus.clk);bus.M_EN = 0;bus.reset_n = 0;
   	@(negedge bus.clk);
	//IDLE state checking
	//RESET state checking
	@(negedge bus.clk);bus.M_EN = 1;bus.reset_n = 0;
	@(negedge bus.clk);
	// $display("%0t",$time,"RESET state checking::Clock=%0d,reset=%0d,bus.M_EN=%0d,bus.SCL =%0d, bus.ack_n =%0d, ,bus.SDA_OUT =%0d,State =%0s,NextState =%0s,temp_SCL=%0d", bus.clk,bus.reset_n,bus.M_EN,bus.SCL,bus.ack_n,bus.SDA_OUT,DUT.State,DUT.NextState, DUT.temp_scl);
	
 end
 endtask
 
 task startsequence(input logic datareadyt,input logic [7:0] dataint, input logic [6:0] addrt, input logic rwt);
 begin
 @(negedge bus.clk);
    bus.reset_n = 1;
    bus.data_rdy =datareadyt;
	bus.F_Out = dataint;
	bus.ADDR= addrt;
	bus.R_W=rwt;
	// $display("%0t Start SEQUENCE temp_data =%b, bus.F_Out = %b,temp_addr=%b,bus.ADDR=%b, bus.R_W=%b,temp_r_w =%b", $time,DUT.temp_data,bus.F_Out,DUT.temp_addr,bus.ADDR, bus.R_W, DUT.temp_r_w);
 end
 endtask
 
 task send_address;
 begin
 $display("\nCollecting Address");
 repeat(8)
	begin
	@(negedge bus.clk);
	end
	@(negedge bus.clk);
	bus.ack_n ='0;
	bus.reset_n = 1;
	
	// $display("%0t",$time,"addr bus.ack_n recieved from mem contr", bus.ack_n);//140
	// $display("%0t",$time,"Send addr SEQUENCE checking::Clock=%0d,reset=%0d,bus.M_EN=%0d,bus.SCL =%0d, bus.ack_n =%0d,bus.SDA_OUT=%0d, State =%0s,NextState =%0s,temp_SCL=%0d", bus.clk,bus.reset_n,bus.M_EN,bus.SCL,bus.ack_n,bus.SDA_OUT,DUT.State,DUT.NextState, DUT.temp_scl);
	@(negedge bus.clk) bus.ack_n = 1;bus.data_rdy ='0;
	end
 endtask
 
 task readwrite;
 begin
 $display("\nCollecting Data");
	repeat(8)@(negedge bus.clk);
	wait_counter = 0;
	// @(negedge bus.clk);
	@(negedge bus.clk);
	bus.ack_n ='0;
	// $display("%0t Data Ack recieved from memory controller after write state",$time);
 end
 endtask
 
 task stopseq;
 begin
    @(negedge bus.clk);
	@(negedge bus.clk);
	// $display("%0t sequence stopped state = %s",$time,DUT.NextState);
 
 end
 endtask
 
 task stopreadseq;
 begin
    @(negedge bus.clk);
	bus.ack_n ='0;
    @(negedge bus.clk);
	@(negedge bus.clk);
	// $display("%0t sequence stopped state = %s",$time,DUT.NextState);
 end
 endtask
 
 task ApplyWriteStimulus(input logic datareadyt,input logic [7:0] dataint, input logic [6:0] addrt, input logic rwt);
	begin
	resettask;
	startsequence(datareadyt,dataint,addrt,rwt);
	send_address;
	readwrite;
	stopseq;
	end
 endtask
 
 task ApplyReadStimulus(input logic datareadyt,input logic [7:0] dataint, input logic [6:0] addrt, input logic rwt);
	begin
	resettask;
	startsequence(datareadyt,dataint,addrt,rwt);
	send_address;
	stopreadseq;
	end
 endtask
 
 
 i2c DUT(.bus(bus.master));
  
 initial
 begin
    bus.clk = 0;
	forever #5 bus.clk = ~bus.clk;
 end 
  initial 
  begin 
    
	
	// WRITE TESTING 
	ApplyWriteStimulus(1,2,3,1);

	//read
	ApplyReadStimulus(1,2,3,0);

 
	$stop; 
  end
 
endmodule