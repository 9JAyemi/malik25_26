// SVA for the provided design. Bind to top_module.

module top_module_sva
(
  input logic        clk,
  input logic        rst,
  input logic        up_down,
  input logic        A,B,C,D,E,F,G,
  input logic [3:0]  count,
  input logic [6:0]  seg_display,
  input logic [6:0]  final_output
);

  default clocking cb @(posedge clk); endclocking

  // 7-seg golden model
  function automatic logic [6:0] segmap (input logic [3:0] d);
    case (d)
      4'h0: segmap = 7'b1111110;
      4'h1: segmap = 7'b0110000;
      4'h2: segmap = 7'b1101101;
      4'h3: segmap = 7'b1111001;
      4'h4: segmap = 7'b0110011;
      4'h5: segmap = 7'b1011011;
      4'h6: segmap = 7'b1011111;
      4'h7: segmap = 7'b1110000;
      4'h8: segmap = 7'b1111111;
      4'h9: segmap = 7'b1111011;
      default: segmap = 7'b0000001;
    endcase
  endfunction

  // Basic sanity: no X/Z on key signals when not in reset
  assert property (disable iff (rst) !$isunknown({up_down,count,seg_display,final_output,A,B,C,D,E,F,G}));

  // Counter reset behavior (synchronous)
  assert property (rst |=> count == 4'h0);
  assert property (rst && $past(rst) |-> count == 4'h0);

  // Counter step behavior (mod-16 up/down)
  assert property (disable iff (rst)
                   $past(!rst) |-> ( $past(up_down)
                                     ? count == $past(count) + 4'h1
                                     : count == $past(count) - 4'h1 ));

  // 7-seg mapping correct for all nibble values
  assert property (seg_display == segmap(count));

  // A..G must mirror seg_display bus mapping
  assert property ({A,B,C,D,E,F,G} == seg_display);

  // Bitwise OR output correctness (count zero-extends to 7 bits)
  assert property (final_output == ({3'b000, count} | seg_display));

  // Coverage

  // Exercise both directions
  cover property (disable iff (rst) $past(!rst) &&  $past(up_down) && count == $past(count)+1);
  cover property (disable iff (rst) $past(!rst) && !$past(up_down) && count == $past(count)-1);

  // Wrap-around in both directions
  cover property (disable iff (rst) $past(up_down)  && $past(count)==4'hF && count==4'h0);
  cover property (disable iff (rst) !$past(up_down) && $past(count)==4'h0 && count==4'hF);

  // Visit all 16 counter values
  genvar i;
  generate
    for (i=0;i<16;i++) begin : cov_all_counts
      cover property (disable iff (rst) count == i[3:0]);
    end
  endgenerate

  // See at least one non-decimal 7-seg "error" pattern
  cover property (disable iff (rst) count inside {[4'hA:4'hF]} && seg_display == 7'b0000001);

endmodule

bind top_module top_module_sva i_top_module_sva
(
  .clk(clk),
  .rst(rst),
  .up_down(up_down),
  .A(A), .B(B), .C(C), .D(D), .E(E), .F(F), .G(G),
  .count(count),
  .seg_display(seg_display),
  .final_output(final_output)
);