// SVA for priority_encoder
module priority_encoder_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        in0, in1, in2, in3,
  input  logic [1:0]  out,
  input  logic        valid
);
  wire [3:0] bus = {in3,in2,in1,in0};

  // Async reset drives outputs low immediately and holds them while reset is high
  assert property (@(posedge reset) (out==2'b00 && valid==1'b0));
  assert property (@(posedge clk) reset |-> (out==2'b00 && valid==1'b0));

  // Clocking/disable defaults for the rest
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Outputs never X/Z when not in reset
  assert property (!$isunknown({out,valid}));

  // valid follows OR of inputs (one-cycle latency due to sequential sampling)
  assert property ((bus==4'b0000) |=> (valid==1'b0));
  assert property ((bus!=4'b0000) |=> (valid==1'b1));

  // One-hot encodings (registered)
  assert property ((bus==4'b0001) |=> (out==2'b00 && valid));
  assert property ((bus==4'b0010) |=> (out==2'b01 && valid));
  assert property ((bus==4'b0100) |=> (out==2'b10 && valid));
  assert property ((bus==4'b1000) |=> (out==2'b11 && valid));

  // Zero-hot and multi-hot hold last out; valid per spec
  assert property ((bus==4'b0000)          |=> (out==$past(out) && !valid));
  assert property ((!$onehot0(bus))        |=> (out==$past(out) &&  valid));

  // Out changes only when prior inputs were one-hot
  assert property ((out != $past(out)) |-> $past($onehot(bus)));

  // Coverage: exercise key scenarios
  cover property ((bus==4'b0001) |=> (out==2'b00 && valid));
  cover property ((bus==4'b0010) |=> (out==2'b01 && valid));
  cover property ((bus==4'b0100) |=> (out==2'b10 && valid));
  cover property ((bus==4'b1000) |=> (out==2'b11 && valid));
  cover property ((bus==4'b0000) |=> (!valid));
  cover property ((!$onehot0(bus)) |=> valid);
endmodule

// Bind to DUT
bind priority_encoder priority_encoder_sva u_priority_encoder_sva (
  .clk(clk), .reset(reset),
  .in0(in0), .in1(in1), .in2(in2), .in3(in3),
  .out(out), .valid(valid)
);