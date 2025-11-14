// SVA for parity_checker
// Bind this checker to the DUT
bind parity_checker parity_checker_sva sva_i (.*);

module parity_checker_sva (input logic [2:0] data, input logic parity);

  // Functional check (deferred immediate to allow delta-cycle settle)
  always @* begin
    assert (#0 (parity === (data[0] ^ data[1] ^ data[2])))
      else $error("parity mismatch: parity=%0b data=%0b", parity, data);

    // No X/Z on parity when inputs are known
    if (!$isunknown(data))
      assert (#0 !$isunknown(parity))
        else $error("X/Z on parity for known data: data=%0b parity=%0b", data, parity);

    // Functional coverage: all input combinations with expected parity
    cover (data==3'b000 && parity==1'b0);
    cover (data==3'b001 && parity==1'b1);
    cover (data==3'b010 && parity==1'b1);
    cover (data==3'b011 && parity==1'b0);
    cover (data==3'b100 && parity==1'b1);
    cover (data==3'b101 && parity==1'b0);
    cover (data==3'b110 && parity==1'b0);
    cover (data==3'b111 && parity==1'b1);
  end

  // Edge coverage on parity
  cover property (@(posedge parity) 1);
  cover property (@(negedge parity) 1);

endmodule