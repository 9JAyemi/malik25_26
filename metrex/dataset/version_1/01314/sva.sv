// SVA for top_module
// Quality-focused, concise checks and coverage

module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic        pwm,
  input logic [3:0]  counter,
  input logic [7:0]  compare_value,
  input logic [3:0]  gray_code,
  input logic [2:0]  highest_priority,
  input logic [1:0]  pos,
  input logic [3:0]  encoder_out
);

  default clocking cb @(posedge clk); endclocking

  // helpers
  bit past_valid;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  logic eq_hit_now, eq_hit_past;
  always_comb eq_hit_now = ({4'b0000, counter} == compare_value); // match DUT compare width
  always_ff @(posedge clk or posedge reset) begin
    if (reset) eq_hit_past <= 1'b0;
    else       eq_hit_past <= eq_hit_now;
  end

  // async reset takes effect immediately
  assert property (@(posedge reset) (counter==4'd0 && compare_value==8'd125 && pwm==1'b0));

  // hold reset values while asserted
  assert property (cb reset |-> (counter==4'd0 && compare_value==8'd125 && pwm==1'b0)
                             and $stable({counter,compare_value,pwm}));

  // compare_value must be stable when not in reset
  assert property (cb disable iff (reset) $stable(compare_value));

  // counter/pwm update rules
  assert property (cb past_valid &&  eq_hit_past |-> counter==4'd0);
  assert property (cb past_valid && !eq_hit_past |-> counter==$past(counter)+4'd1);

  assert property (cb past_valid &&  eq_hit_past |-> pwm==~$past(pwm));
  assert property (cb past_valid && !eq_hit_past |-> pwm==$past(pwm));

  // counter range
  assert property (cb counter inside {[4'd0:4'd15]});

  // combinational mappings
  assert property (cb gray_code[0] ==  encoder_out[0]);
  assert property (cb gray_code[1] == (encoder_out[0]^encoder_out[1]));
  assert property (cb gray_code[2] == (encoder_out[1]^encoder_out[2]));
  assert property (cb gray_code[3] == (encoder_out[2]^encoder_out[3]));

  assert property (cb gray_code==4'b0001 |-> highest_priority==3'b001);
  assert property (cb gray_code==4'b0010 |-> highest_priority==3'b010);
  assert property (cb gray_code==4'b0100 |-> highest_priority==3'b100);
  assert property (cb !(gray_code inside {4'b0001,4'b0010,4'b0100}) |-> highest_priority==3'b000);

  assert property (cb highest_priority inside {3'b000,3'b001,3'b010,3'b100});

  assert property (cb highest_priority==3'b001 |-> pos==2'b01);
  assert property (cb highest_priority==3'b010 |-> pos==2'b10);
  assert property (cb highest_priority==3'b100 |-> pos==2'b11);
  assert property (cb !(highest_priority inside {3'b001,3'b010,3'b100}) |-> pos==2'b00);

  // no X after reset deasserted
  assert property (cb disable iff (reset) !$isunknown({pwm,counter,compare_value,gray_code,highest_priority,pos}));

  // coverage
  cover property (cb past_valid && eq_hit_past); // equality/toggle event
  cover property (cb past_valid && $past(counter)==4'hF && counter==4'h0); // natural 4-bit wrap
  cover property (cb gray_code==4'b0001 && pos==2'b01);
  cover property (cb gray_code==4'b0010 && pos==2'b10);
  cover property (cb gray_code==4'b0100 && pos==2'b11);
  cover property (cb !(gray_code inside {4'b0001,4'b0010,4'b0100}) && pos==2'b00);

endmodule

bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset(reset),
  .pwm(pwm),
  .counter(counter),
  .compare_value(compare_value),
  .gray_code(gray_code),
  .highest_priority(highest_priority),
  .pos(pos),
  .encoder_out(encoder_out)
);