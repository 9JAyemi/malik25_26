// SVA for rj45_led_controller
// Focus: protocol, FSM, clocking, outputs, and data-path correctness
// Bind into DUT for access to internals

module rj45_led_controller_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Sanity / combinational relations
  assert property (!$isunknown({rj45_led_sck, rj45_led_sin, rj45_led_lat, rj45_led_blk}));
  assert property (rj45_led_blk == 1'b0);
  assert property (rj45_led_sin == output_shifter[15]);
  assert property (rj45_led_lat == latch);
  assert property (rj45_led_sck == (clk_div2[CLK_DIV] & clk_enable));
  assert property (busy == (busy_int | read_req | write_req));
  assert property (state inside {IDLE, READ, WRITE});

  // Reset effects
  assert property (reset |=> (state==IDLE && clk_enable==0 && output_shifter==16'h0 &&
                              write_counter==5'h0 && latch==0 && busy_int==1 &&
                              value_cache==32'd0 && clk_div1==0 && clk_div2==0));

  // Clock divider behavior and update_out
  assert property (clk_div2 == $past(clk_div1));
  assert property (clk_div1 == $past(clk_div1) + 1);
  assert property (update_out == ($past(clk_div1[CLK_DIV]) && !clk_div1[CLK_DIV])); // negedge detect

  // Request handling / FSM
  assert property ((state==IDLE && write_req) |=> (state==WRITE && busy_int==1 &&
                   write_counter==5'd0 &&
                   value_cache=={24'd0, data_write[7:0]} &&
                   output_shifter=={1'b0, data_write[0], 1'b0, data_write[1],
                                    1'b0, data_write[2], 1'b0, data_write[3],
                                    1'b0, data_write[4], 1'b0, data_write[5],
                                    1'b0, data_write[6], 1'b0, data_write[7]}));
  assert property ((state==IDLE && read_req) |=> (state==READ && busy_int==1));
  assert property (state==READ |=> (state==IDLE && busy_int==0 && data_read==$past(value_cache)));
  assert property ((state==IDLE && write_req && read_req) |=> state==WRITE); // WRITE priority
  assert property ((state==WRITE) |-> busy_int==1);
  assert property ((state==IDLE && !write_req && !read_req) |-> busy_int==0);

  // WRITE sequencing driven by update_out
  assert property ((state==WRITE && !update_out) |=> $stable(write_counter));
  assert property ((state==WRITE && update_out) |=> (write_counter == $past(write_counter)+1));
  assert property ((state==WRITE && update_out && $past(write_counter)==0) |=> (clk_enable==1));
  assert property ((state==WRITE && update_out && $past(write_counter) inside {[1:15]})
                   |=> (output_shifter == {$past(output_shifter)[14:0], 1'b0}));
  assert property ((state==WRITE && update_out && $past(write_counter)==16)
                   |=> (clk_enable==0 && latch==1 && state==WRITE)); // latch assert cycle
  assert property (latch |-> (state==WRITE && write_counter==5'd17)); // latch holds until next pulse
  assert property ((state==WRITE && update_out && $past(write_counter)>16)
                   |=> (state==IDLE && latch==0 && busy_int==0)); // write complete

  // SCK gating
  assert property ((!clk_enable) |-> (rj45_led_sck==1'b0));
  assert property ((clk_enable)  |-> (rj45_led_sck==clk_div2[CLK_DIV]));

  // Coverage
  cover property (state==IDLE && write_req ##1 state==WRITE
                  ##[1:$] (update_out && $past(write_counter)==16) ##1 latch
                  ##[1:$] (update_out && $past(write_counter)==17) ##1 state==IDLE);

  cover property (state==IDLE && read_req ##1 state==READ ##1 state==IDLE);

  cover property ($fell(clk_div1[CLK_DIV]) && update_out); // divider negedge observed
endmodule

bind rj45_led_controller rj45_led_controller_sva sva_inst();