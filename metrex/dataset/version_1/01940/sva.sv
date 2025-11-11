// SVA for counter
module counter_sva #(parameter WIDTH=4)
(
  input logic                iCLK,
  input logic                iRST,
  input logic [WIDTH-1:0]    oCNT
);

  default clocking cb @(posedge iCLK); endclocking
  localparam logic [WIDTH-1:0] ZERO = '0;
  localparam logic [WIDTH-1:0] ONE  = {{(WIDTH-1){1'b0}},1'b1};
  localparam logic [WIDTH-1:0] MAX  = {WIDTH{1'b1}};

  // Sanity: no X on key signals at clock edges
  a_known: assert property (disable iff ($initstate)
                            !$isunknown(iRST) && !$isunknown(oCNT));

  // Synchronous reset: next-cycle state is 0 when reset was high
  a_reset_clears: assert property (disable iff ($initstate)
                                   $past(iRST) |-> (oCNT == ZERO));

  // Normal operation: modulo increment when not in reset on prior cycle
  a_inc: assert property (disable iff ($initstate)
                          $past(!iRST) |-> (oCNT == ($past(oCNT) + ONE)));

  // After reset deassertion, first counted value is 1
  a_post_reset_first1: assert property (disable iff ($initstate)
                                        $fell(iRST) |=> (oCNT == ONE));

  // Coverage
  c_reset_assert:   cover property ($rose(iRST));
  c_reset_deassert: cover property ($fell(iRST));
  c_wrap:           cover property (disable iff ($initstate)
                                    $past(!iRST) && ($past(oCNT) == MAX) && (oCNT == ZERO));
  c_full_run_16:    cover property (!iRST[*16]); // 16 consecutive count cycles

endmodule

bind counter counter_sva #(.WIDTH(4)) counter_sva_i (.iCLK(iCLK), .iRST(iRST), .oCNT(oCNT));