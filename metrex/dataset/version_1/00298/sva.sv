// SVA for bin_to_gray
module bin_to_gray_sva (
  input logic        clk,
  input logic        rst,
  input logic [3:0]  BIN,
  input logic [3:0]  GRAY
);
  default clocking cb @(posedge clk); endclocking

  function automatic logic [3:0] f_gray(input logic [3:0] b);
    return b ^ (b >> 1);
  endfunction

  // Sanity/cleanliness
  a_rst_known: assert property ( !$isunknown(rst) )
    else $error("rst is X/Z");
  a_in_known_when_used: assert property ( !rst |-> !$isunknown(BIN) )
    else $error("BIN is X/Z when used");
  a_out_known_when_inputs_known: assert property ( !rst && !$isunknown(BIN) |-> !$isunknown(GRAY) )
    else $error("GRAY is X/Z with known inputs");

  // Functional correctness
  a_reset_clears: assert property ( rst |-> GRAY == 4'b0000 )
    else $error("GRAY not cleared on reset");
  a_map_now: assert property ( !rst |-> GRAY == f_gray(BIN) )
    else $error("GRAY != BIN^(BIN>>1)");

  // Temporal sanity
  a_same_in_same_out: assert property ( !rst && $past(!rst) && BIN == $past(BIN)
                                        |-> GRAY == $past(GRAY) )
    else $error("Output changed while input held constant");

  // Gray adjacency when BIN steps by ±1 (mod 16)
  a_adjacent_onebit: assert property (
      !rst && $past(!rst) &&
      ( (BIN == $past(BIN) + 4'd1) || (BIN + 4'd1 == $past(BIN)) )
      |-> $countones(GRAY ^ $past(GRAY)) == 1
    ) else $error("GRAY not 1-bit adjacent for BIN +/-1");

  // Coverage
  c_reset_deassert: cover property ( rst ##1 !rst );
  c_correct_min:    cover property ( !rst && BIN==4'h0 && GRAY==4'h0 );
  c_correct_max:    cover property ( !rst && BIN==4'hF && GRAY==4'h8 );
  c_inc_onebit:     cover property ( !rst && $past(!rst) &&
                                     BIN == $past(BIN) + 4'd1 &&
                                     $countones(GRAY ^ $past(GRAY)) == 1 );

  // Toggle coverage per GRAY bit
  genvar i;
  generate
    for (i=0;i<4;i++) begin : g_cov_gray_toggles
      c_gray_bit_toggle: cover property ( !rst && $changed(GRAY[i]) );
    end
  endgenerate
endmodule

// Bind into DUT
bind bin_to_gray bin_to_gray_sva u_bin_to_gray_sva (.clk(clk), .rst(rst), .BIN(BIN), .GRAY(GRAY));