// SVA for decoder
module decoder_sva (
  input  logic [1:0] in,
  input  logic       enable,
  input  logic [3:0] out
);

  // Core combinational equivalence and structural checks (delta-cycle aligned)
  always_comb begin
    assert #0 (out === (enable ? 4'b0000 : (4'b0001 << in)))
      else $error("decoder: functional mismatch");

    assert #0 ($onehot0(out))
      else $error("decoder: out must be onehot or zero");

    assert #0 ((|out) == ~enable)
      else $error("decoder: OR(out) must equal ~enable");

    if (!$isunknown({in, enable})) begin
      assert #0 (!$isunknown(out))
        else $error("decoder: out has X/Z with known inputs");
    end

    // Functional coverage
    cover (!enable && in==2'b00 && out==4'b0001);
    cover (!enable && in==2'b01 && out==4'b0010);
    cover (!enable && in==2'b10 && out==4'b0100);
    cover (!enable && in==2'b11 && out==4'b1000);
    cover ( enable && out==4'b0000);
  end

  // Temporal reaction (delta-cycle) to control/data changes
  assert property (@(posedge enable)  ##0 (out==4'b0000))
    else $error("decoder: out not zero on enable↑");

  assert property (@(negedge enable)  ##0 (out==(4'b0001<<in)))
    else $error("decoder: decode not asserted on enable↓");

  assert property (@(in)  enable  |-> ##0 (out==4'b0000))
    else $error("decoder: out changed with in while enabled");

  assert property (@(in) !enable |-> ##0 (out==(4'b0001<<in)))
    else $error("decoder: decode not tracking in when disabled");
endmodule

// Bind into DUT
bind decoder decoder_sva u_decoder_sva (.in(in), .enable(enable), .out(out));