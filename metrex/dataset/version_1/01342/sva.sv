// SVA checker for DecoEscrituraRegistros (bindable, clockless, concise)
module DecoEscrituraRegistros_sva (
  input  logic        Write,
  input  logic [8:0]  Address,
  input  logic [21:0] EnableRegister,
  input  logic        EnableStart
);

  // Golden decode
  function automatic logic [21:0] decode(input logic [8:0] a, input logic w);
    logic [21:0] d;
    d = '0;
    if (w) begin
      d[0]  = (a==9'h00C);
      d[1]  = (a==9'h010);
      d[2]  = (a==9'h014);
      d[3]  = (a==9'h018);
      d[4]  = (a==9'h01C);
      d[5]  = (a==9'h020);
      d[6]  = (a==9'h024);
      d[7]  = (a==9'h028);
      d[8]  = (a==9'h02C);
      d[9]  = (a==9'h030);
      d[10] = (a==9'h034);
      d[11] = (a==9'h038);
      d[12] = (a==9'h03C);
      d[13] = (a==9'h040);
      d[14] = (a==9'h044);
      d[15] = (a==9'h048);
      d[16] = (a==9'h04C);
      d[17] = (a==9'h050);
      d[18] = (a==9'h054);
      d[19] = (a==9'h058);
      d[20] = (a==9'h05C);
      d[21] = (a==9'h060);
    end
    return d;
  endfunction

  // Assertions (combinational, immediate)
  always_comb begin
    // Outputs known
    assert (!$isunknown({EnableStart,EnableRegister}))
      else $error("X/Z detected on outputs");

    // Exact decode equivalence
    assert (EnableRegister === decode(Address, Write))
      else $error("EnableRegister decode mismatch");

    // EnableStart correctness
    assert (EnableStart === (Address==9'h08C))
      else $error("EnableStart decode mismatch");

    // One-hot-or-zero on decoded enables
    assert ($onehot0(EnableRegister))
      else $error("EnableRegister not onehot0");

    // No enables when Write==0
    if (!Write) assert (EnableRegister=='0)
      else $error("EnableRegister not zero when Write==0");

    // Start should never coincide with any register enable
    assert (!(EnableStart && |EnableRegister))
      else $error("EnableStart overlaps EnableRegister");
  end

  // Functional coverage
  // Start pulse coverage
  cover (Address==9'h08C && EnableStart);

  // Per-register decode coverage
  cover (Write && Address==9'h00C && EnableRegister[0]);
  cover (Write && Address==9'h010 && EnableRegister[1]);
  cover (Write && Address==9'h014 && EnableRegister[2]);
  cover (Write && Address==9'h018 && EnableRegister[3]);
  cover (Write && Address==9'h01C && EnableRegister[4]);
  cover (Write && Address==9'h020 && EnableRegister[5]);
  cover (Write && Address==9'h024 && EnableRegister[6]);
  cover (Write && Address==9'h028 && EnableRegister[7]);
  cover (Write && Address==9'h02C && EnableRegister[8]);
  cover (Write && Address==9'h030 && EnableRegister[9]);
  cover (Write && Address==9'h034 && EnableRegister[10]);
  cover (Write && Address==9'h038 && EnableRegister[11]);
  cover (Write && Address==9'h03C && EnableRegister[12]);
  cover (Write && Address==9'h040 && EnableRegister[13]);
  cover (Write && Address==9'h044 && EnableRegister[14]);
  cover (Write && Address==9'h048 && EnableRegister[15]);
  cover (Write && Address==9'h04C && EnableRegister[16]);
  cover (Write && Address==9'h050 && EnableRegister[17]);
  cover (Write && Address==9'h054 && EnableRegister[18]);
  cover (Write && Address==9'h058 && EnableRegister[19]);
  cover (Write && Address==9'h05C && EnableRegister[20]);
  cover (Write && Address==9'h060 && EnableRegister[21]);

  // Negative decode coverage (valid write to unmapped address yields no enables)
  cover ( Write
          && !(Address inside {
                9'h00C,9'h010,9'h014,9'h018,9'h01C,9'h020,9'h024,9'h028,9'h02C,
                9'h030,9'h034,9'h038,9'h03C,9'h040,9'h044,9'h048,9'h04C,9'h050,
                9'h054,9'h058,9'h05C,9'h060})
          && (EnableRegister=='0) );

endmodule

// Bind into DUT
bind DecoEscrituraRegistros DecoEscrituraRegistros_sva u_deco_escritura_registros_sva (
  .Write(Write),
  .Address(Address),
  .EnableRegister(EnableRegister),
  .EnableStart(EnableStart)
);