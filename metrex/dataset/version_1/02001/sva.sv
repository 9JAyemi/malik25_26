// SVA checker for bcd_to_7seg
module bcd_to_7seg_sva (
  input logic        clk,
  input logic        reset,
  input logic [2:0]  stage,
  input logic [6:0]  SEG,
  input logic [3:0]  BCD,
  input logic [3:0]  bcd_reg
);

default clocking cb @(posedge clk); endclocking

function automatic logic [6:0] seg_of_stage (logic [2:0] s);
  case (s)
    3'd0: seg_of_stage = 7'b0111111;
    3'd1: seg_of_stage = 7'b0000110;
    3'd2: seg_of_stage = 7'b1011011;
    3'd3: seg_of_stage = 7'b1001111;
    3'd4: seg_of_stage = 7'b1100110;
    3'd5: seg_of_stage = 7'b1101101;
    3'd6: seg_of_stage = 7'b1111101;
    3'd7: seg_of_stage = 7'b0000111;
    default: seg_of_stage = 'x;
  endcase
endfunction

// Reset hold
assert property (reset |-> (stage==3'd0 && SEG==7'b0000000));

// Known-ness when not in reset
assert property (!reset |-> (!$isunknown(stage) && !$isunknown(SEG)));
assert property (!reset |-> !$isunknown(bcd_reg));

// Stage steps 0..7 and wraps
assert property ((!reset && !$past(reset)) |-> stage == (($past(stage)==3'd7) ? 3'd0 : $past(stage)+3'd1));

// SEG shows value for previous stage (combinationally driven from stage)
assert property (!reset |-> SEG == seg_of_stage($past(stage)));

// After reset deasserts, first active cycle: stage=1, SEG shows stage 0 pattern
assert property ($past(reset) && !reset |-> (stage==3'd1 && SEG==seg_of_stage(3'd0)));

// bcd_reg functional intent
assert property (!reset |-> (stage==3'd0 -> bcd_reg==BCD));
assert property (!reset && !$isunknown($past(stage)) |-> bcd_reg == (($past(stage)==3'd0) ? BCD : ($past(bcd_reg)<<1)));

// Legal SEG encodings only
assert property (!reset |-> (SEG inside {
  7'b0111111,7'b0000110,7'b1011011,7'b1001111,
  7'b1100110,7'b1101101,7'b1111101,7'b0000111
}));

// Coverage
cover property (disable iff (reset)
  stage==3'd0 ##1 stage==3'd1 ##1 stage==3'd2 ##1 stage==3'd3 ##
  1 stage==3'd4 ##1 stage==3'd5 ##1 stage==3'd6 ##1 stage==3'd7 ##1 stage==3'd0);

cover property ($past(reset) && !reset);

endmodule

// Bind into DUT (accesses internal stage and bcd_reg)
bind bcd_to_7seg bcd_to_7seg_sva i_bcd_to_7seg_sva(
  .clk(clk),
  .reset(reset),
  .stage(stage),
  .SEG(SEG),
  .BCD(BCD),
  .bcd_reg(bcd_reg)
);