module FunctionalUnitTest;

mainbus bus();
parameter TRUE=1;
parameter FALSE=0;

parameter enable_display_testcase_pass_or_fail = FALSE; // Update value to TRUE to display if each testcase is passed or failed

parameter DEBUG = FALSE; // Update value to TRUE to display the values for each testcase

// bit bus.clk;
// bit bus.reset_n;
// logic [7:0] bus.F_In;
// logic [2:0] bus.S;
// logic bus.MSBIn;
// logic bus.LSBIn;
// logic bus.M_en;

// logic [7:0] bus.F_Out;
logic [7:0] exp_F_Out;

int i,j;

int err_cnt=0;

FunctionalUnit DUT(.bus(bus.functional_unit));
ref_FunctionalUnit ref_DUT(exp_F_Out, data_rdy, bus.clk, bus.reset_n, bus.F_In, bus.S, bus.MSBIn, bus.LSBIn, bus.M_en);

always #5 bus.clk = ~bus.clk;

initial 
begin

	//Testing basic operations in testcases 1-9
	// Test case 1: bus.reset_n the register 
	@(negedge bus.clk);
	bus.M_en = 1;
	#1;
	bus.reset_n=0;
	repeat(3)@(negedge bus.clk);
	compare_outputs;
	display_inp_outp_values;
	display_pass_or_fail(1);
  
	// Test case 2: bus.S=0, expecting No change in the outputs 
	@(negedge bus.clk);
	bus.reset_n=1; 
	bus.F_In=8'bx; 
	bus.S=3'b000;
	repeat(3)@(negedge bus.clk);
	compare_outputs;
	display_inp_outp_values;
	display_pass_or_fail(2);
  
	// Test case 3: Loading input to the register
	@(negedge bus.clk);
	bus.S=3'b001; 
	bus.F_In=8'b10101010;
	compare_outputs;
	repeat(3)@(negedge bus.clk);
	display_inp_outp_values;
	display_pass_or_fail(3);
	
	// Test case 4: Logical shift right with same input
	@(negedge bus.clk);
	bus.S=3'b010;
	bus.MSBIn=1'b0;
	compare_outputs;
	repeat(3)@(negedge bus.clk);
	display_inp_outp_values;
	display_pass_or_fail(4);
	
	// Test case 5: Logical shift left after the output from logical shift right
	@(negedge bus.clk);
	bus.S=3'b011;
	bus.LSBIn=1'b1;
	compare_outputs;
	repeat(3)@(negedge bus.clk);
	display_inp_outp_values;
	display_pass_or_fail(5);
	
	// Test case 6: Rotate right after the output from logical shift right
	@(negedge bus.clk);
	bus.S=3'b100;
	compare_outputs;
	repeat(3)@(negedge bus.clk);
	display_inp_outp_values;
	display_pass_or_fail(6);
	
	// Test case 7: Rotate left after rotate right
	@(negedge bus.clk);
	bus.S=3'b101;
	compare_outputs;
	repeat(3)@(negedge bus.clk);
	display_inp_outp_values;
	display_pass_or_fail(7);
	
	// Test case 8: Arithmetic shift right after rotate left
	@(negedge bus.clk);
	bus.S=3'b110;
	compare_outputs;
	repeat(3)@(negedge bus.clk);
	display_inp_outp_values;
	display_pass_or_fail(8);
	
	// Test case 9: Arithmetic shift left after Arithmetic shift right
	@(negedge bus.clk);
	bus.S=3'b111;
	compare_outputs;
	repeat(3)@(negedge bus.clk);
	display_inp_outp_values;
	display_pass_or_fail(9);
	
	// Testcase10: Testing all combinations for bus.S, bus.F_In with bus.MSBIn,bus.LSBIn = x/0/1
	for(i=0; i<8; i++)
	begin
	  @(negedge bus.clk);
	  bus.S=i;
	  for(j=0; j<256; j++)
	  begin
	    @(negedge bus.clk);
	    bus.F_In=j;
		bus.MSBIn=1'b1;
		bus.LSBIn=1'bx;
		repeat(3)@(negedge bus.clk);
		compare_outputs;
		
		@(negedge bus.clk);
		bus.MSBIn=1'b0;
		bus.LSBIn=1'bx;
		repeat(3)@(negedge bus.clk);
		compare_outputs;
		
		@(negedge bus.clk);
		bus.MSBIn=1'bx;
		bus.LSBIn=1'b1;
		repeat(3)@(negedge bus.clk);
		compare_outputs;
		
		@(negedge bus.clk);
		bus.MSBIn=1'bx;
		bus.LSBIn=1'b0;
		repeat(3)@(negedge bus.clk);
		compare_outputs;
		
		@(negedge bus.clk);
		bus.MSBIn=1'bx;
		bus.LSBIn=1'bx;
		repeat(3)@(negedge bus.clk);
		compare_outputs;
		display_inp_outp_values;
		
	  end
	end
	display_pass_or_fail(10);
		
	
	// Test case 11: Parallel load and logical shift right with different input values and different bus.MSBIn
	@(negedge bus.clk);
	bus.S=3'b001;
	for(i=0; i<2; i++)
	begin
	  bus.MSBIn=i;
	  for(j=0; j<256; j++)
	    begin
	      @(negedge bus.clk);
	      bus.F_In=j;
	  	  bus.S=3'b010;
		  repeat(3)@(negedge bus.clk);
	  	  compare_outputs;
	  	  display_inp_outp_values;
	    end
	end
	display_pass_or_fail(11);
  
	// Test case 12: Parallel load and logical shift left with different input values and different bus.LSBIn
	@(negedge bus.clk);
	bus.S=3'b001;
	for(i=0; i<2; i++)
	begin
	  bus.MSBIn=1'bx;
	  bus.LSBIn=i;
	  for(j=0; j<256; j++)
	    begin
	      @(negedge bus.clk);
	      bus.F_In=j;
	  	  bus.S=3'b011;
		  repeat(3)@(negedge bus.clk);
	  	  compare_outputs;
	  	  display_inp_outp_values;
	    end
	end
	display_pass_or_fail(12);
  
	// Test case 13: Logical Shift left and rotate right with input 11001100
	@(negedge bus.clk);
	bus.S=3'b001;
	for(i=0; i<2; i++)
	begin
	  bus.LSBIn=i;
	  bus.F_In=8'b11001100;
	  @(negedge bus.clk);
	  bus.S=3'b011;
	  repeat(2)@(negedge bus.clk);
	  bus.S=3'b100;
	  repeat(3)@(negedge bus.clk);
	  compare_outputs;
	  display_inp_outp_values;
	end
	display_pass_or_fail(13);
	
	// Test case 14: Rotate left and arithmetic shift right with parallel load as 10001100
	bus.S=3'b001;
	bus.F_In=8'b10001100;
	@(negedge bus.clk);
	bus.S=3'b101;
	@(negedge bus.clk);
	bus.S=3'b110;
	repeat(3)@(negedge bus.clk);
	compare_outputs;
	display_inp_outp_values;
	display_pass_or_fail(14);
	
	// Test case 15: Arithmetic shift left and logical shift right and shift for 3 bus.clk cycles
	@(negedge bus.clk);
	bus.S=3'b110;
	@(negedge bus.clk);
	bus.MSBIn=1'b1;
	bus.S=3'b10;
	repeat(3)@(negedge bus.clk);
	repeat(3)@(negedge bus.clk);
	compare_outputs;
	display_inp_outp_values;
	display_pass_or_fail(15);
	
	// Test case 16: Parallel load and rotate left with different input values
	@(negedge bus.clk);
	bus.S=3'b001;
	for(j=0; j<256; j++)
	  begin
	    @(negedge bus.clk);
	    bus.F_In=j;
		bus.S=3'b101;
		repeat(8)@(negedge bus.clk);
		repeat(3)@(negedge bus.clk);
		compare_outputs;
		display_inp_outp_values;
	  end
	display_pass_or_fail(16);
	
	// Test case 17: Logical shift right and rotate right
	@(negedge bus.clk);
	bus.S=3'b001;
	for(i=0; i<2; i++)
	begin
	  bus.LSBIn=i;
	  bus.F_In=8'b11001100;
	  @(negedge bus.clk);
	  bus.S=3'b010;
	  repeat(6)@(negedge bus.clk);
	  bus.S=3'b100;
	  repeat(3)@(negedge bus.clk);
	  compare_outputs;
	  display_inp_outp_values;
	end
	display_pass_or_fail(17);
	
	// Test case 18: Rotate left, arithmetic shift left, 2 logical shift lefts
	@(negedge bus.clk);
	bus.S=3'b101;
	@(negedge bus.clk);
	bus.S=3'b111;
	@(negedge bus.clk);
	bus.S=3'b011;
	repeat(2)@(negedge bus.clk);
	repeat(3)@(negedge bus.clk);
	compare_outputs;
	display_inp_outp_values;
	display_pass_or_fail(18);
	
	// Test case 19: Parallel load with no change for 3 cycles, then rotate right 
	@(negedge bus.clk);
	bus.S=3'b001;
	bus.F_In=8'b01111111;
	@(negedge bus.clk);
	bus.S=3'b000;
	repeat(3)@(negedge bus.clk);
	bus.S=3'b100;
	repeat(8)@(negedge bus.clk);
	repeat(3)@(negedge bus.clk);
	compare_outputs;
	display_inp_outp_values;
	display_pass_or_fail(19);


	repeat(10) @(negedge bus.clk);
	if(err_cnt!==0) $display("\n * TESTING SHIFT REGISTER FAILED, Total number of testcases failed = %0d\n",err_cnt);
	else $display("\n --- All testcases are passed for ShiftRegister\n");
	
	@(negedge bus.clk);
	$stop;
end


task display_inp_outp_values;
	if(DEBUG)
	begin
	  @(negedge bus.clk);
	  $strobe("bus.F_In= %b, bus.S= %b, MSB = %b, LSB = %b, bus.F_Out = %b, exp_F_Out=%b", bus.F_In,bus.S,bus.MSBIn,bus.LSBIn,bus.F_Out,exp_F_Out);
	end
endtask:display_inp_outp_values


task compare_outputs;
	@(negedge bus.clk);
	if(bus.F_Out!==exp_F_Out) 
	begin
	  $strobe("bus.F_In= %b, bus.S= %b, MSB = %b, LSB = %b, Exp_out is exp_F_Out=%b, Got output is bus.F_Out = %b", bus.F_In,bus.S,bus.MSBIn,bus.LSBIn,exp_F_Out,bus.F_Out);
	  err_cnt++;
	end
	else err_cnt = err_cnt; 
endtask:compare_outputs


task display_pass_or_fail(input int n);
	if(bus.F_Out!==exp_F_Out && err_cnt>0) $display("\n---Testcase%0d Failed---",n);
	else if(err_cnt===0 && enable_display_testcase_pass_or_fail) $display("\n---Testcase%0d Passed---",n);
endtask:display_pass_or_fail


endmodule



// Golden model for shift register
module ref_FunctionalUnit(F_Out, data_rdy, clk, reset_n, F_In, S, MSBIn, LSBIn, M_en);

parameter Nbits = 8;

output logic  [Nbits-1:0] F_Out;
output logic  data_rdy;

input  logic clk;
input  logic reset_n;
input  logic [Nbits-1:0] F_In;
input  logic [2:0] S;
input  logic MSBIn;
input  logic LSBIn;
input logic M_en;


typedef enum logic[4:0] {IDLE = 5'b00001,RESET = 5'b00010,COMPUTE_LOGIC = 5'b00100,SEND_OUT = 5'b01000,DISABLE = 5'b10000}  state_type;

state_type State, Next_state;

logic [Nbits-1:0]temp_reg;

always_ff @(posedge clk or negedge reset_n)
	begin 
	if(M_en)
		begin
		if (!reset_n) State <= RESET;
		else	State <= Next_state;
		end
	else State <= IDLE;
	end

//always_ff @(posedge clk) 
always_comb
begin   

unique case(State)
	IDLE         :	if(M_en)
						Next_state = RESET;
					else
						begin 
						F_Out = 'z;
						data_rdy = 'z;
						Next_state = IDLE;
						end
						
	RESET 		 :	if(reset_n) 
						Next_state = COMPUTE_LOGIC;
					else
						begin 
						F_Out = '0;
						data_rdy = '0;
						Next_state = RESET;
						end				
		
	COMPUTE_LOGIC:	begin
					for (int i = 0; i < Nbits; i = i + 1) begin
					case(S)
						3'b000: temp_reg[i] <= temp_reg[i]; // no change
						3'b001: temp_reg[i] <= F_In[i]; // parallel load
						3'b010: temp_reg[i] <= (i == Nbits-1) ? MSBIn : temp_reg[i+1]; // logical shift right
						3'b011: temp_reg[i] <= (i == 0) ? LSBIn : temp_reg[i-1]; // logical shift left
						3'b100: temp_reg[i] <= (i == Nbits-1) ? temp_reg[0] : temp_reg[i+1]; // rotate right
						3'b101: temp_reg[i] <= (i == 0) ? temp_reg[Nbits-1] : temp_reg[i-1]; // rotate left
						3'b110: temp_reg[i] <= (i == Nbits-1) ? temp_reg[Nbits-1] : temp_reg[i+1]; // arithmetic shift right
						3'b111: temp_reg[i] <= (i == 0) ? 1'b0 : temp_reg[i-1]; // arithmetic shift left
					endcase
					end
						Next_state = SEND_OUT;
					end	
		
	SEND_OUT	 :	begin
					F_Out = temp_reg;
					data_rdy <= '1;
					Next_state = DISABLE;
					end
			
	DISABLE		 : 	begin
					data_rdy = 0;
					Next_state = IDLE;
					end
	endcase
end	


endmodule