// SVA checker for binary_to_gray. Bind this to the DUT.
module binary_to_gray_sva #(parameter WIDTH=4) (
  input  logic [WIDTH-1:0] bin,
  input  logic [WIDTH-1:0] gray
);

  // Functional equivalence (combinational, allow delta cycle for propagation)
  property p_gray_map;
    @(bin) !$isunknown(bin) |-> ##0 (gray == (bin ^ (bin >> 1)));
  endproperty
  a_gray_map: assert property (p_gray_map)
    else $error("binary_to_gray mismatch: bin=%0h gray=%0h exp=%0h",
                bin, gray, (bin ^ (bin >> 1)));

  // No X/Z on output when inputs are known
  a_no_x: assert property (@(bin) !$isunknown(bin) |-> ##0 !$isunknown(gray))
    else $error("binary_to_gray produced X/Z for known input: bin=%0h gray=%0h", bin, gray);

  // Functional coverage: hit all 2^WIDTH input values and corresponding outputs
  genvar v;
  for (v = 0; v < (1<<WIDTH); v++) begin : COV_ALL_CODES
    localparam logic [WIDTH-1:0] VBIN  = v[WIDTH-1:0];
    localparam logic [WIDTH-1:0] VGRAY = VBIN ^ (VBIN >> 1);
    cover property (@(bin) ##0 (bin === VBIN && gray === VGRAY));
  end

endmodule

// Bind to the DUT
bind binary_to_gray binary_to_gray_sva #(.WIDTH(4)) u_binary_to_gray_sva (.bin(bin), .gray(gray));