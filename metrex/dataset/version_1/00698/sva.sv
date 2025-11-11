// SVA bind module for my_module (handles SV keyword 'do' via escaped identifier)
module my_module_sva (
  input logic [7:0] di,
  input logic [7:0] doo
);
  // Vector-level checks (4-state safe)
  always_comb begin
    assert (doo[4:0] === di[4:0])
      else $error("my_module: do[4:0] != di[4:0] di=%0h do=%0h", di, doo);
    assert (doo[7:5] === ~di[7:5])
      else $error("my_module: do[7:5] != ~di[7:5] di=%0h do=%0h", di, doo);
  end

  // Bitwise localization + functional coverage
  genvar i;
  generate
    for (i=0;i<5;i++) begin : FWD
      always_comb
        assert (doo[i] === di[i])
          else $error("my_module: forward bit %0d mismatch di=%0b do=%0b", i, di[i], doo[i]);
      cover property (@(di[i] or doo[i]) ##0 (di[i]===0 && doo[i]===0));
      cover property (@(di[i] or doo[i]) ##0 (di[i]===1 && doo[i]===1));
    end
    for (i=5;i<8;i++) begin : INV
      always_comb
        assert (doo[i] === ~di[i])
          else $error("my_module: invert bit %0d mismatch di=%0b do=%0b", i, di[i], doo[i]);
      cover property (@(di[i] or doo[i]) ##0 (di[i]===0 && doo[i]===1));
      cover property (@(di[i] or doo[i]) ##0 (di[i]===1 && doo[i]===0));
    end
  endgenerate

  // Whole-bus functional cover
  cover property (@(di or doo) ##0 (doo[4:0]===di[4:0] && doo[7:5]===~di[7:5]));
endmodule

// Bind into the DUT (escaped identifier for 'do')
bind my_module my_module_sva sva_my_module (.di(di), .doo(\do ));