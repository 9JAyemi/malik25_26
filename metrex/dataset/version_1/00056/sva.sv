// SVA for barrel_shifter_4bit
// Bind-in checker; pure combinational, concise, and complete

module barrel_shifter_4bit_sva (
    input logic [3:0] DATA_IN,
    input logic [1:0] SHIFT,
    input logic [3:0] DATA_OUT
);

  function automatic [3:0] exp (input logic [3:0] d, input logic [1:0] s);
    case (s)
      2'b00: exp = d;
      2'b01: exp = {d[3], d[2:0]};
      2'b10: exp = {d[2:0], d[3]};
      2'b11: exp = {d[1:0], d[3:2]};
    endcase
  endfunction

  // X/Z checks
  always @* begin
    assert (!$isunknown({SHIFT, DATA_IN}))
      else $error("barrel_shifter_4bit: X/Z on inputs SHIFT=%b DATA_IN=%b", SHIFT, DATA_IN);
    assert (!$isunknown(DATA_OUT))
      else $error("barrel_shifter_4bit: X/Z on DATA_OUT");
  end

  // Functional equivalence
  always @* begin
    logic [3:0] e = exp(DATA_IN, SHIFT);
    assert (DATA_OUT === e)
      else $error("barrel_shifter_4bit: Mismatch SHIFT=%b DATA_IN=%b EXP=%b GOT=%b",
                  SHIFT, DATA_IN, e, DATA_OUT);
  end

  // Minimal functional coverage
  always @* begin
    cover (SHIFT == 2'b00 && DATA_OUT === DATA_IN);
    cover (SHIFT == 2'b01 && DATA_OUT === {DATA_IN[3], DATA_IN[2:0]});
    cover (SHIFT == 2'b10 && DATA_OUT === {DATA_IN[2:0], DATA_IN[3]});
    cover (SHIFT == 2'b11 && DATA_OUT === {DATA_IN[1:0], DATA_IN[3:2]});
  end

endmodule

bind barrel_shifter_4bit barrel_shifter_4bit_sva u_barrel_shifter_4bit_sva (
  .DATA_IN(DATA_IN),
  .SHIFT  (SHIFT),
  .DATA_OUT(DATA_OUT)
);