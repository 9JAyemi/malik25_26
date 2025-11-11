// SVA for MAC_REG_ACC
module MAC_REG_ACC_sva (
  input               clk,
  input               reset,
  input               waitrequest,
  input       [31:0]  readdata,
  input       [7:0]   address,
  input               write,
  input               read,
  input       [31:0]  writedata,
  input       [1:0]   current_state,
  input       [2:0]   reg_count,
  input       [3:0]   count
);
  // State encodings (mirror DUT)
  localparam idle_s      = 2'b00;
  localparam wait_clk_s  = 2'b01;
  localparam write_s     = 2'b10;
  localparam wait_s      = 2'b11;

  default clocking cb @(posedge clk); endclocking
  // Active-low reset
  `define DISABLE disable iff (!reset)

  // Basic state sanity
  assert property (`DISABLE (current_state inside {idle_s, wait_clk_s, write_s, wait_s}));

  // Reset values
  assert property (`DISABLE (!reset |-> current_state==wait_clk_s
                                      && address==8'h00 && write==1'b0 && read==1'b0
                                      && writedata==32'h0 && reg_count==3'd0 && count==4'd0));

  // wait_clk_s behavior
  assert property (`DISABLE (current_state==wait_clk_s |-> reg_count==3'd0));
  assert property (`DISABLE (current_state==wait_clk_s && $past(current_state==wait_clk_s)
                             |-> count == $past(count)+1));
  // On entry to wait_clk_s, must reach idle within 16 cycles
  assert property (`DISABLE (current_state==wait_clk_s && $past(current_state)!=wait_clk_s
                             |-> ##[1:16] current_state==idle_s));

  // idle_s outputs and progress/hold
  assert property (`DISABLE (current_state==idle_s |-> address==8'h00 && write==1'b0
                                                  && read==1'b0 && writedata==32'h0 && count==4'd0));
  assert property (`DISABLE (current_state==idle_s && reg_count<3'd4
                             |-> ##1 (current_state==write_s && reg_count==$past(reg_count)+1)));
  assert property (`DISABLE (current_state==idle_s && reg_count>=3'd4
                             |-> ##1 (current_state==idle_s && reg_count==$past(reg_count))));

  // write_s behavior: next state and programmed values
  assert property (`DISABLE (current_state==write_s |-> ##1 current_state==wait_s));
  assert property (`DISABLE (current_state==write_s && reg_count==3'd1
                             |-> address==8'h02 && writedata==32'h1000093 && write==1));
  assert property (`DISABLE (current_state==write_s && reg_count==3'd2
                             |-> address==8'h0e && writedata==32'h4 && write==1));
  assert property (`DISABLE (current_state==write_s && reg_count==3'd3
                             |-> address==8'h94 && writedata==32'h7 && write==1));
  assert property (`DISABLE (current_state==write_s && reg_count>=3'd4
                             |-> address==8'h02 && writedata==32'h1000093));

  // wait_s handshake: write asserted, addr/data stable, completion to idle
  assert property (`DISABLE (current_state==wait_s |-> write==1));
  assert property (`DISABLE (current_state==wait_s && $past(current_state==wait_s)
                             |-> address==$past(address) && writedata==$past(writedata)));
  assert property (`DISABLE (current_state==wait_s && waitrequest==1'b0
                             |-> ##1 current_state==idle_s));

  // No write outside write/wait states; read always 0
  assert property (`DISABLE ((current_state inside {idle_s, wait_clk_s}) |-> write==1'b0));
  assert property (`DISABLE (read==1'b0));

  // Coverage: four programmed writes in order; exercise both wait stretched and immediate completion
  cover property (`DISABLE (current_state==wait_s && address==8'h02)
                               ##[1:10] (current_state==wait_s && address==8'h0e)
                               ##[1:10] (current_state==wait_s && address==8'h94)
                               ##[1:10] (current_state==wait_s && address==8'h02)));
  cover property (`DISABLE (current_state==wait_s && waitrequest ##1
                            current_state==wait_s && waitrequest ##1
                            current_state==wait_s && !waitrequest ##1 current_state==idle_s));
  cover property (`DISABLE (current_state==wait_s && !waitrequest ##1 current_state==idle_s));
endmodule

// Bind into DUT
bind MAC_REG_ACC MAC_REG_ACC_sva sva_i (
  .clk(clk),
  .reset(reset),
  .waitrequest(waitrequest),
  .readdata(readdata),
  .address(address),
  .write(write),
  .read(read),
  .writedata(writedata),
  .current_state(current_state),
  .reg_count(reg_count),
  .count(count)
);