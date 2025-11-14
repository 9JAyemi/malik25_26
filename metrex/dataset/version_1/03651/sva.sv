// SVA checker for bin2gray. Bind this to the DUT.
module bin2gray_sva (
  input logic [3:0] binary,
  input logic [3:0] gray
);

  // Combinational sampling event on any input/output change
  event comb_evt;
  always @(binary or gray) -> comb_evt;

  // No X/Z on output when input is known
  ap_no_x: assert property (@(comb_evt) !$isunknown(binary) |-> !$isunknown(gray));

  // Functional specification: gray == binary ^ (binary >> 1)
  ap_func: assert property (@(comb_evt) gray == (binary ^ (binary >> 1)));

  // Bitwise checks (helpful for localization)
  ap_b3: assert property (@(comb_evt) gray[3] ==  binary[3]);
  ap_b2: assert property (@(comb_evt) gray[2] == (binary[3] ^ binary[2]));
  ap_b1: assert property (@(comb_evt) gray[1] == (binary[2] ^ binary[1]));
  ap_b0: assert property (@(comb_evt) gray[0] == (binary[1] ^ binary[0]));

  // Dependency check: gray only changes when binary changes
  ap_no_spurious_toggle: assert property (@(comb_evt) $changed(gray) |-> $changed(binary));

  // Coverage: see all 16 input/output mappings
  genvar i;
  for (i = 0; i < 16; i++) begin : map_cov
    localparam logic [3:0] BIN = i[3:0];
    localparam logic [3:0] GRY = BIN ^ (BIN >> 1);
    cp_map: cover property (@(comb_evt) (binary == BIN) && (gray == GRY));
  end

endmodule

// Bind the checker to the DUT
bind bin2gray bin2gray_sva u_bin2gray_sva(.binary(binary), .gray(gray));