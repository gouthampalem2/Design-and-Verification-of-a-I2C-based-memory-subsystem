module memorycontroller(mainbus.slave bus);
parameter ADDR_WIDTH = 7;
parameter DATA_WIDTH = 8;

logic reset_done = 0;
logic addr_recvd,data_recvd,r_w_in;
logic[ADDR_WIDTH-1:0] temp_addr;
logic[DATA_WIDTH-1:0] temp_data;
bit counter_reset, wait_cnt_en;
bit get_addr, get_data;

logic [DATA_WIDTH-1:0]data_from_memory;
logic [ADDR_WIDTH-1:0] mem_addr;
logic [DATA_WIDTH-1:0] data_to_memory;


logic [DATA_WIDTH-1:0] memory [(2**ADDR_WIDTH)-1:0];

int count = 0, wait_counter, temp_i = 0;

typedef enum bit [4:0] {RESET=5'b00000,
				  IDLE = 5'b00001,
				  GET_ADDRESS = 5'b00010,
				  READ = 5'b00100,
				  WRITE = 5'b01000,
				  STOP = 5'b10000} state_type;

state_type State, Next;

always_ff@(posedge bus.clk)
begin

Immediateassertion1: assert(!$isunknown({bus.reset_n,bus.clk}))
							 else $error("Immediateassertion1:reset and clock are unknown");
							 
				

	if(!bus.reset_n)
		begin
		//$display("%0t, Inside RESET", $time);
		State <= IDLE;
		wait_counter <= 0;
		end
	else 
		begin
		State <= Next;
		if(wait_cnt_en)
			begin
			// $strobe("%0t wait_cnt_en enabled, wait_counter = %0d", $time,wait_counter);
			wait_counter <= wait_counter + 1;
			// $strobe("%0t wait_counter incremented, wait_counter = %0d", $time, wait_counter);
			end
		else
			wait_counter <= 0;
		end
end
	
always_comb
begin
	Next = State;
	addr_recvd = addr_recvd; 
	data_recvd = data_recvd; 
	counter_reset = 0;
	bus.ack_n = 1;
	//$display("%0t, Inside always_comb", $time);
	unique case (State)
	RESET       :	begin
					if(!bus.reset_n) Next = RESET;
					else Next = IDLE;
					end

	IDLE		:	begin
					//$display("%0t, Inside IDLE State",$time);
						wait_cnt_en = 1;
						if(wait_counter >= 1)
							begin
							if(!bus.SDA_OUT) // checking start sequence
								begin
								//$display("Start Sequence detected");
								addr_recvd = 0;
								data_recvd = 0;
								Next = GET_ADDRESS;
								wait_cnt_en = 0;
								end
							else
								begin
								counter_reset = 0;
								addr_recvd=0;
								data_recvd=0;
								Next = IDLE;
								end
							end
					else
						begin
						Next = IDLE;
						addr_recvd=0;
						data_recvd=0;
						end
					//$display("End of IDLE state");
					end


		
	GET_ADDRESS	:	begin
					//$display("Start of GET_ADDRESS, value of wait_counter = %0d", wait_counter);
					wait_cnt_en = 1;
					if(wait_counter<=6)
						begin
						//$display("Start of wait_counter<=6 in GET_ADDRESS");
						temp_addr[wait_counter] = bus.SDA_OUT;
						//$display("%0t temp_addr updated, temp_addr[%0d] = %0d, temp_addr = %0d",$time,wait_counter, temp_addr[wait_counter], temp_addr);
						Next=GET_ADDRESS;
						//$display("End of wait_counter<=6 in GET_ADDRESS");
						end
					else if(wait_counter >6 && wait_counter <= 7)
						begin
						//$display("Start of wait_counter>6 && wait_counter<=7in GET_ADDRESS");
						r_w_in = bus.SDA_OUT;
						Next= GET_ADDRESS;
						//$display("%0t r_w_in updated, %0d",$time, r_w_in);
						if(wait_counter == 7 && r_w_in)
							begin
							//$display("Start of wait_counter==7 && r_w_in in GET_ADDRESS");
							mem_addr = temp_addr;
							addr_recvd = 1;
							data_recvd = 0;
							bus.ack_n = '0;
							Next = WRITE;
							wait_cnt_en = 0;
							//$display("End of wait_counter==7 && r_w_in in GET_ADDRESS");
							end
						else if(wait_counter ==7 && !r_w_in)
							begin
							//$display("Start of wait_counter==7 && !r_w_in in GET_ADDRESS");
							// temp_addr = 10;
							mem_addr = temp_addr;
							addr_recvd = 1;
							data_recvd = 0;
							bus.ack_n = '0;
							Next = READ;
							wait_cnt_en = 0;
							//$display("End of wait_counter==7 && !r_w_in in GET_ADDRESS");	
							end
						else
							begin
							mem_addr = mem_addr;
							bus.ack_n = bus.ack_n;
							Next = STOP;
							wait_cnt_en = 0;
							//$display("End of wait_counter>6 && wait_counter<=7in GET_ADDRESS");	
							end
						//$display("End of wait_counter>6 && wait_counter<=7in GET_ADDRESS");
						end
					else
							begin
							bus.ack_n = '1;
							Next = STOP;
							wait_cnt_en = 0;
							//$display("End of wait_counter>7 && wait_counter<=8in GET_ADDRESS");	
							end
					//$display("End of GET_ADDRESS");
					end
					
						
	READ		:	begin
					//$display("Read State Started");
					addr_recvd = 1;
					data_recvd = 0;
					Next = STOP;
					//$display("Read State Ended");
					
					end
						
	WRITE		:	begin
					//$display("%0t Write State Started", $time);
					wait_cnt_en = 1;
					if(wait_counter <= 1)
						begin
						//$display("%0t Inside Wait counter <= 1, wait_counter = %0d", $time, wait_counter);
						Next = WRITE;
						end
					else if(wait_counter >1 && wait_counter < 10)
						begin
						//$display("%0t Inside Wait counter >=2 && <10, wait_counter = %0d", $time, wait_counter);
						temp_data[wait_counter-2] = bus.SDA_OUT;
						//$display("%0t temp_data updated, temp_data[wait_counter] = temp_data[%0d] = %0d, SDA_OUT = %0d", $time, wait_counter-2, temp_data[wait_counter-2], bus.SDA_OUT);
						//$display("%0t Collected Data = %0d", $time, temp_data);
						if(wait_counter == 9)
							begin
							addr_recvd = 1;
							data_recvd = 1;
							bus.ack_n = '0;
							// temp_data = 20;
							data_to_memory = temp_data;
							end
						else
							begin
							addr_recvd = 1;
							data_recvd = 0;
							bus.ack_n = bus.ack_n;
							end
						end
					else if(wait_counter >=10 && wait_counter <11)
						begin
						//$display("%0t Inside Wait counter >=10 && <11, wait_counter = %0d", $time, wait_counter);
						addr_recvd = 1;
						data_recvd = 1;
						data_to_memory = temp_data;
						bus.ack_n = '0;
						Next = STOP;
						wait_cnt_en = 0;
						//$display("%0t After acknolwedge, wait_counter = %0d, ack_n = %0d, Next+%0p", $time, wait_counter, bus.ack_n, Next);
						//$display("%0t Write State Ended", $time);
						end
					else
						begin
						wait_cnt_en = 0;
						Next = STOP;
						end
					
					end
			
	
	STOP		:	begin
					wait_cnt_en = 1;
					//$display("STOP started, wait_counter = %0d", wait_counter);
					if(wait_counter >= 1)
						begin
						//$display("Inside wait_counter>=1, wait_counter = %0d", wait_counter);
							//$display("Inside !SDA_OUT && SCL>=1, wait_counter = %0d, SCL = %0d, SDA_OUT = %0d", wait_counter,bus.SCL, bus.SDA_OUT);
							if(wait_counter >= 2 && bus.SDA_OUT)
								begin
								//$display("\n Inside wait_counter >= 2");
								Next = IDLE;
								wait_cnt_en = 0;
								//$display("%0t Stop sequence detected, SDA_OUT = %0d, Next = %p", $time, bus.SDA_OUT, Next);
								end
							else
								begin
								//$display("%0t Else of wait_counter>=2 && SDA_OUT, wait_counter=%0d SCL = %0d, SDA_OUT = %0d", $time, wait_counter,bus.SCL, bus.SDA_OUT);
								Next = STOP;
								end
						end
					else
						begin
						//$display("%0t Else of wait_counter>=1, wait_counter = %0d, SCL = %0d, SDA_OUT = %0d", $time, wait_counter,bus.SCL, bus.SDA_OUT);
						Next = STOP;
						end
						end
	endcase
end

always_ff@(posedge bus.clk)
begin
	if(!bus.reset_n)
		begin
		bus.data_out <= 0;
		bus.done <= 0;
		end
	else 
		begin
		if(addr_recvd && !data_recvd)
			begin
			if(!r_w_in)
				bus.data_out <= memory[mem_addr];
			else if(r_w_in)
				begin
				memory[mem_addr] = memory[mem_addr];
				bus.data_out <= bus.data_out;
				end
			else
				begin
				memory[mem_addr] <= memory[mem_addr];
				bus.data_out <= bus.data_out;
				end
			end
		else if(addr_recvd && data_recvd)
		begin
			if(!r_w_in)
				memory[mem_addr] <= memory[mem_addr];
			else if(r_w_in)
				begin
				memory[mem_addr] = data_to_memory;
				memory[100] = 200;  // Hardcoded value
				end
			else
				begin
				memory[mem_addr] <= memory[mem_addr];
				bus.data_out <= bus.data_out;
				end
			end
		else
			begin
			memory[mem_addr] <= memory[mem_addr];
			bus.data_out <= bus.data_out;
			end
		end
end


endmodule