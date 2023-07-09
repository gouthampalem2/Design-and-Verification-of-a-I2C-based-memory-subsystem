module FunctionalUnit(mainbus.functional_unit bus);
// mainbus bus();

parameter Nbits = 8;

// logic  [Nbits-1:0] bus.F_Out;
// logic  bus.data_rdy;

// logic bus.clk;
// logic bus.reset_n;
// logic [Nbits-1:0] bus.F_In;
// logic [2:0] bus.S;
// logic bus.MSBIn;
// logic bus.LSBIn;
// logic bus.M_en;

property p_1din;
	@(posedge bus.clk) (!bus.reset_n) |-> (bus.F_Out == '0 && bus.data_rdy == '0);
	endproperty
	counterassertion1_din: assert property(p_1din)
							else $error("counterassertion_p1: fout and dataready are not becoming zero after reset");
	
	
	
	
property p_4din;
	@(posedge bus.clk) (bus.S == 1) |-> !($isunknown(bus.F_In));
	endproperty
	counterassertion4_din: assert property(p_4din)
						   else $error("counterassertion_fin: The data input bus value Fin is unknown during a load operation");


typedef enum logic[4:0] {IDLE = 5'b00001,RESET = 5'b00010,COMPUTE_LOGIC = 5'b00100,SEND_OUT = 5'b01000,DISABLE = 5'b10000}  state_type;

state_type State, Next_state;

logic [Nbits-1:0]temp_reg;

always_ff @(posedge bus.clk or negedge bus.reset_n)
	begin 
	Immediateassertion1: assert(!$isunknown({bus.reset_n,bus.clk}))
							 else $error("Immediateassertion1: reset and clock are unknown");
	if(bus.M_en)
		begin
		if (!bus.reset_n) State <= RESET;
		else	State <= Next_state;
		end
	else State <= IDLE;
	end

//always_ff @(posedge bus.clk) 
always_comb
begin   

unique case(State)
	IDLE         :	if(bus.M_en)
						Next_state = RESET;
					else
						begin 
						bus.F_Out = 'z;
						bus.data_rdy = 'z;
						Next_state = IDLE;
						end
						
	RESET 		 :	if(bus.reset_n) 
						Next_state = COMPUTE_LOGIC;
					else
						begin 
						$display("Inside else of Reset");
						bus.F_Out = '0;
						bus.data_rdy = '0;
						Next_state = RESET;
						end				
		
	COMPUTE_LOGIC:	begin
					case (bus.S)
						3'b000: temp_reg <= temp_reg; // no change
						3'b001: temp_reg <= bus.F_In; // parallel load
						3'b010: temp_reg <= {bus.MSBIn, temp_reg[Nbits-1:1]}; //temp_reg <= {bus.MSBIn, temp_reg[7:1]}; // logical shift right
						3'b011: temp_reg <= {temp_reg[Nbits-2:0], bus.LSBIn}; //temp_reg <= {temp_reg[6:0], bus.LSBIn}; // logical shift left
						3'b100: temp_reg <= {temp_reg[0], temp_reg[Nbits-1:1]}; //temp_reg <= {temp_reg[0], temp_reg[7:1]}; // rotate right
						3'b101: temp_reg <=  {temp_reg[Nbits-2:0], temp_reg[Nbits-1]}; //{temp_reg[6:0], temp_reg[7]}; // rotate left
						3'b110: temp_reg <= {temp_reg[Nbits-1], temp_reg[Nbits-1:1]}; //{temp_reg[7], temp_reg[7:1]}; // arithmetic shift right
						3'b111: temp_reg <= {temp_reg[Nbits-2:0], 1'b0}; //{temp_reg[6:0], 1'b0}; // arithmetic shift left
						endcase
						Next_state = SEND_OUT;
					end	
		
	SEND_OUT	 :	begin
					bus.F_Out = temp_reg;
					bus.data_rdy <= '1;
					Next_state = DISABLE;
					end
			
	DISABLE		 : 	begin
					bus.data_rdy = 0;
					Next_state = IDLE;
					end
	endcase
end	

endmodule