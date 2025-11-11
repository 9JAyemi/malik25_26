// SVA checker for top_module
module top_module_sva (
  input  [2:0] a,
  input  [2:0] b,
  input        c,
  input        control,
  input        select,
  input  [2:0] out_and_bitwise,
  input        out_and_logical,
  input  [2:0] out_xor,
  input  [5:0] out_not,
  input  [3:0] out_mux
);

  // Functional correctness (4-state exact checks)
  always_comb begin
    assert (out_and_bitwise === (a & b)) else $error("and_bitwise mismatch");
    assert (out_and_logical === ((a != 0) && (b != 0))) else $error("and_logical mismatch");
    assert (out_xor        === (a ^ b)) else $error("xor mismatch");

    assert (out_not[5:3] === ~a) else $error("out_not[5:3] != ~a");
    assert (out_not[2:0] === ~b) else $error("out_not[2:0] != ~b");

    // Mux behavior for 0/1/XZ select and width-extension bit
    if (select === 1'b0) begin
      assert (out_mux[2:0] === a) else $error("mux sel=0 mismatch");
    end else if (select === 1'b1) begin
      assert (out_mux[2:0] === b) else $error("mux sel=1 mismatch");
    end else begin
      assert (out_mux[2:0] === (a ^ b)) else $error("mux sel=X/Z mismatch");
    end
    assert (out_mux[3] === 1'b0) else $error("out_mux[3] must be 0 (3->4 assign)");
  end

  // Outputs depend only on a,b,select (c/control are unused)
  always @* if ($changed({c,control}) && $stable({a,b,select}))
    assert ($stable({out_and_bitwise, out_and_logical, out_xor, out_not, out_mux}))
      else $error("Outputs changed due to c/control");

  // Combinational stability: if driving inputs stable, outputs must be stable
  always @* if ($stable({a,b,select}))
    assert ($stable({out_and_bitwise, out_and_logical, out_xor, out_not, out_mux}))
      else $error("Combinational outputs changed without input change");

  // Minimal functional coverage
  always_comb begin
    cover (select === 1'b0);
    cover (select === 1'b1);
    cover (!(select===1'b0) && !(select===1'b1)); // X/Z path to xor_result

    cover (a == 3'b000);
    cover (b == 3'b000);
    cover (a == b);
    cover (a == ~b);

    cover (out_and_logical == 1'b0);
    cover (out_and_logical == 1'b1);

    cover (out_xor == 3'b000);
    cover (out_and_bitwise == 3'b000);
    cover (out_and_bitwise != 3'b000);

    cover ($changed({c,control}) && $stable({a,b,select})); // exercise independence
  end

endmodule

// Bind SVA to DUT
bind top_module top_module_sva sva_i (.*);