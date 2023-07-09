module i2c(mainbus.master bus);

parameter DATA_WIDTH=8;
parameter ADDR_WIDTH=7;

logic [ADDR_WIDTH-1:0]temp_addr;
logic [DATA_WIDTH-1:0]temp_data ;
logic temp_scl;
logic temp_r_w;

logic scl_seq;

enum logic[4:0] {RESET  = 5'b00001, START_SEQUENCE=5'b00010,
          SEND_ADDRESS = 5'b00100, READ_WRITE = 5'b01000, STOP =5'b10000} State, NextState;

int temp_i = 0;
int count = 0;
int wait_counter;
bit wait_cnt_en;

always_ff@(posedge bus.clk)
begin

Immediateassertion1: assert(!$isunknown({bus.reset_n,bus.clk}))
							 else $error("Immediateassertion1: reset and clock are unknown");

//$display("Simulation started");
if(bus.M_EN)
	begin
	if (!bus.reset_n)  
		begin
		State <= RESET;
		wait_counter <= 0;
		end
	else
		begin
		State <= NextState;
		if(wait_cnt_en)
			begin
			wait_counter <= wait_counter +1;
			end
		else
			wait_counter <= 0;
		end
	end
else  
	State <= START_SEQUENCE;
end  

always_comb
begin 
    if(bus.M_EN)
	begin
	unique case (State)
	      
	RESET: begin
	assert_reset_state: assert property (@(posedge bus.clk)
    disable iff(!bus.M_EN)($rose(!bus.reset_n) |-> (State == RESET)));
             if(!bus.reset_n)  // reset =0
                 begin
				//$display("IF RESET STARTED");
                    temp_scl=1;
                    bus.SDA_OUT =1;
                    NextState= RESET; 
				end    
             else 
				begin
				//$display("RESET State Endeded");
                     NextState = START_SEQUENCE;
					//$display("%0t, state =%s, NextState =%s", $time, State, NextState);
				end	 
		   end
		   
	START_SEQUENCE: begin 
			if(!bus.reset_n) //reset =0
				begin
				NextState=RESET;  
				end
			else //reset =1
				begin
				if(bus.data_rdy)
					begin 
					bus.SDA_OUT = '0;//SENDING START SEQUENCE
					NextState=SEND_ADDRESS;
					temp_data =bus.F_Out;
					temp_addr =bus.ADDR;
					temp_r_w  =bus.R_W;
					//$display("%0t Detected data ready and add is recieved from Fun unit",$time);
						assert_start_condition: assert property (@(posedge bus.SCL)
                    disable iff(!bus.reset_n || !bus.M_EN)(bus.SDA_OUT === 1'b1 && $past(bus.SDA_OUT) === 1'b1) |-> (bus.SDA_OUT === 1'b0));	
					end

				else 
					begin
					bus.SDA_OUT = bus.SDA_OUT;
					temp_data='z;
					temp_addr='z;
					temp_r_w='z;	
					NextState = START_SEQUENCE;		
					//$display("%0t data ready not  Detected",$time);
					end	
				end
			end

	SEND_ADDRESS:begin  
                if(!bus.reset_n)	
					begin 
					NextState=RESET;  	
					//$display("%0t Inside bus.reset_n in Send Address state",$time);
					end
				else  
					begin
					//$display("%0t Address seq is started and continued",$time);
					wait_cnt_en = 1;
					// if(wait_counter <=6)
					if(wait_counter <=(ADDR_WIDTH-1))
						begin
						bus.SDA_OUT = temp_addr[wait_counter];
						$display("%0t bus.SDA_OUT VALUE is %0d and temp_addr[wait_counter] = temp_addr[%0d] = %0d", $time, bus.SDA_OUT, wait_counter, temp_addr[wait_counter]);
						NextState = SEND_ADDRESS;
						//$display("value =%0d", wait_counter);
						end
					// else if(wait_counter >6 && wait_counter <=7)
					else if(wait_counter >(ADDR_WIDTH-1) && wait_counter <=ADDR_WIDTH)
						begin
						//$display("Address sent and  raed write signal detected %0d", wait_counter);
						bus.SDA_OUT = temp_r_w;
						NextState = SEND_ADDRESS;
						//$display("%0t bus.SDA_OUT VALUE is %0d and temp_r_w = %0d", $time, bus.SDA_OUT, temp_r_w);
						//$display("End of wait_counter >=7 && wait_counter < 8, value =%0d, bus.SDA_OUT = %0d *", wait_counter, bus.SDA_OUT); //7
						end
					// else if (wait_counter > 7 && wait_counter <=8)
					else if (wait_counter > ADDR_WIDTH && wait_counter <=(ADDR_WIDTH+1))
						begin
							if(!bus.ack_n)
							begin
								//$display("%0t,After Sending ADDRESS ACK is recieved from mem contr bus.ack_n =%0b",$time, bus.ack_n);
								NextState = READ_WRITE;
								wait_cnt_en = 0;
								//wait_counter
								//$display("%0t, state =%s, NextState =%s", $time, State, NextState);
								//bus.ack_n ='1;
								//$display("%0t,SEND ADDRESS ACK ENDED CHECKING bus.ack_n-0- =%0b", $time,bus.ack_n);
								//$display("%0t, state =%s, NextState =%s", $time, State, NextState);
							end	
							else
								begin
								wait_cnt_en = 0;
								NextState =  READ_WRITE;
								//$display("%0t,After Sending ADDRESS waiting for ACK from mem contr bus.ack_n =%0b",$time, bus.ack_n);

								end
						end
					else
						begin
						wait_cnt_en = 0;
						NextState = SEND_ADDRESS;
						//$display("%0t Adress mismatch not in the range",$time);
						end
					end
				end 	
			
	READ_WRITE: begin
				if(!bus.reset_n) //reset condition
					begin
					//$display("%0t, INSIDE READ_WRITE block if reset",$time);
					NextState = RESET;
					end
				else
                    begin 
					//$display("%0t, READ_WRITE STARTED",$time);
                    if(temp_r_w) // write condition
						begin
						wait_cnt_en =1;
						//$display("write condition");
						//$display("%0t",$time," BEFORE if(wait_counter<8)wait_counter =%0d", wait_counter , );
                        // if(wait_counter <= 7)
                        if(wait_counter <= (DATA_WIDTH-1))
							begin
							//$display("Inside wait_counter<=7, wait_counter = %0d", wait_counter);
							bus.SDA_OUT = temp_data[wait_counter];
							NextState = READ_WRITE;
							$display("%0t bus.SDA_OUT VALUE is %0d and temp_data[wait_counter] = temp_data[%0d] = %0d", $time, bus.SDA_OUT, wait_counter, temp_data[wait_counter]);
							//$display("SDA_OUT_DATA = %0d", bus.SDA_OUT);
							end
						else
							begin
							// if(wait_counter >7 && wait_counter <= 9)
							if(wait_counter >(DATA_WIDTH-1) && wait_counter <= (DATA_WIDTH+1))
								begin
								//$display(" Inside wait_counter >7 && wait_counter <= 9, wait_counter = %0d", wait_counter);
								if(!bus.ack_n)
									begin
									//$display("%0t,After Sending data ACK is recieved from mem contr bus.ack_n =%0b",$time, bus.ack_n);

									NextState = STOP; // previously it was NS = IDLE
									wait_cnt_en =1;
									//$display("Checking nextstate after write =%0s", NextState);
									end
								else
									begin
									//$display("Ack not recieved after sending data");
									NextState = READ_WRITE; // previously it was NS = STOP
									wait_cnt_en =1;
									end
								end
							else
								begin
								//$display(" Inside else of wait_counter >7 && wait_counter <= 9,wait_counter = %0d", wait_counter);
								NextState = STOP; //IDLE;
								wait_cnt_en = 0;
								//$display("Data bits are not 8 bits, so invalid data");
								end
							end
						end
					else if(!temp_r_w)// read start
						begin 
						//$display("Inside read condition after sending address");
							if(!bus.ack_n)
									begin
									//$display("%0t,After Sending address add ack is recieved from mem contr bus.ack_n =%0b",$time, bus.ack_n);
									NextState = STOP;
									wait_cnt_en =0;
									//$display("%0t, Checking NextState after read  =%0s", $time, NextState);
									end
								else
									begin
									//$display("%0t Ack is not recieved after sending address and read signal",$time);
									NextState = STOP;//STOP;
									end
								//end
						//NextState = IDLE;
						end
					else
						begin 
						//$display("invalid last bit address , so read and write is not decided");
						NextState = STOP;
						bus.SDA_OUT ='0;
						end
					end	
			end	

	STOP:	begin 
			if(!bus.ack_n)
				begin
				temp_scl<= '1;
				bus.SDA_OUT = '0;
				//$display("Entered stop state bus.SDA_OUT =%0b",bus.SDA_OUT);
				wait_cnt_en =1;
					begin
					if(wait_counter >=1) 
						begin
						bus.SDA_OUT ='1;
						//$display("Stop seq ended SDA =%0b",bus.SDA_OUT);
						assert_stop_condition: assert property (@(posedge bus.clk)
						disable iff(!bus.M_EN)(State == STOP && bus.ack_n == 0) |-> ##1 (bus.SDA_OUT == 1 && temp_scl == 1));
						end
					else 
						begin 
						bus.SDA_OUT ='0;
						//$display("Stop seq not detected SDA =%0b",bus.SDA_OUT);
						end 
					end
				NextState=START_SEQUENCE;
				wait_cnt_en ='0;
				//$display("Whole cycle is ended and waiting for the next data ready signal state = %s", NextState);
				end
			else
				begin
				NextState = STOP; 
				//$display("%0t ack is not detected after sending add or data waiting for ack",$time);
				end
			end
		
     endcase
	 end
	 else begin
         temp_scl='Z;
         bus.SDA_OUT='Z;
		 end
		end
	



 assign bus.SCL = (State ==  RESET || State == STOP) ?  temp_scl : scl_seq;
 assign scl_seq = bus.clk;
	


endmodule