// SVA for gray_to_binary
package gray_to_binary_sva_pkg;
  function automatic logic [3:0] gray2bin4(logic [3:0] g);
    gray2bin4[3] = g[3];
    gray2bin4[2] = g[3]^g[2];
    gray2bin4[1] = g[3]^g[2]^g[1];
    gray2bin4[0] = g[3]^g[2]^g[1]^g[0];
  endfunction
endpackage

module gray_to_binary_assertions
  (input logic [3:0] gray,
   input logic [3:0] binary);
  import gray_to_binary_sva_pkg::*;

  // Combinational functional checks (no race vs DUT always @ (gray))
  always_comb begin
    assert (binary === gray2bin4(gray))
      else $error("gray_to_binary mismatch exp=%0b got=%0b g=%0b", gray2bin4(gray), binary, gray);

    // Bitwise expectations (helpful pinpointing, still concise)
    assert (binary[3] ===  gray[3])                              else $error("b3");
    assert (binary[2] === (gray[3]^gray[2]))                     else $error("b2");
    assert (binary[1] === (gray[3]^gray[2]^gray[1]))             else $error("b1");
    assert (binary[0] === (gray[3]^gray[2]^gray[1]^gray[0]))     else $error("b0");

    // No X/Z in output when input is known
    if (!$isunknown(gray)) assert (!$isunknown(binary))
      else $error("Known gray produced X/Z binary g=%0b b=%0b", gray, binary);
  end

  // Functional coverage: exercise full input/output space and mapping
  covergroup cg @(gray);
    cp_g : coverpoint gray   { bins all[] = {[0:15]}; }
    cp_b : coverpoint binary { bins all[] = {[0:15]}; }
    x_gb : cross cp_g, cp_b; // Expect one-to-one mapping when assertions hold
  endgroup
  cg cg_i = new();
endmodule

// Bind to DUT
bind gray_to_binary gray_to_binary_assertions u_gray_to_binary_assertions (.gray(gray), .binary(binary));