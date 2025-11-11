// SVA for EscrituraRegistroToMemoria
// Uses immediate assertions/coverage (combinational DUT has no clock).
// Bind this file to the DUT instance.

module EscrituraRegistroToMemoria_sva #(parameter Width=4)
(
  input Read, InError, ListoIn,
  input [8:0] Address,
  input signed [Width-1:0] InDato,
  input signed [Width-1:0] Coeff00,Coeff01,Coeff02,Coeff03,Coeff04,Coeff05,
                           Coeff06,Coeff07,Coeff08,Coeff09,Coeff10,Coeff11,Coeff12,Coeff13,Coeff14,
                           Coeff15,Coeff16,Coeff17,Coeff18,Coeff19,
  input signed [Width-1:0] Offset, DatoEntradaSistema,
  input signed [Width-1:0] Y0,Y1,Y2,Y3,Y4,Y5,Y6,Y7,Y8,Y9,
  input signed [Width-1:0] OutDato
);

  // Golden combinational model of OutDato per spec
  function automatic signed [Width-1:0] exp_out;
    begin
      if (Read) begin
        if      (Address==9'h000 && ListoIn) exp_out = signed'(1);
        else if (Address==9'h004)            exp_out = InDato;
        else if (Address==9'h008 && InError) exp_out = signed'(1);
        else if (Address==9'h00C)            exp_out = Coeff00;
        else if (Address==9'h010)            exp_out = Coeff01;
        else if (Address==9'h014)            exp_out = Coeff02;
        else if (Address==9'h018)            exp_out = Coeff03;
        else if (Address==9'h01C)            exp_out = Coeff04;
        else if (Address==9'h020)            exp_out = Coeff05;
        else if (Address==9'h024)            exp_out = Coeff06;
        else if (Address==9'h028)            exp_out = Coeff07;
        else if (Address==9'h02C)            exp_out = Coeff08;
        else if (Address==9'h030)            exp_out = Coeff09;
        else if (Address==9'h034)            exp_out = Coeff10;
        else if (Address==9'h038)            exp_out = Coeff11;
        else if (Address==9'h03C)            exp_out = Coeff12;
        else if (Address==9'h040)            exp_out = Coeff13;
        else if (Address==9'h044)            exp_out = Coeff14;
        else if (Address==9'h048)            exp_out = Coeff15;
        else if (Address==9'h04C)            exp_out = Coeff16;
        else if (Address==9'h050)            exp_out = Coeff17;
        else if (Address==9'h054)            exp_out = Coeff18;
        else if (Address==9'h058)            exp_out = Coeff19;
        else if (Address==9'h05C)            exp_out = Offset;
        else if (Address==9'h060)            exp_out = DatoEntradaSistema;
        else if (Address==9'h064)            exp_out = Y0;
        else if (Address==9'h068)            exp_out = Y1;
        else if (Address==9'h06C)            exp_out = Y2;
        else if (Address==9'h070)            exp_out = Y3;
        else if (Address==9'h074)            exp_out = Y4;
        else if (Address==9'h078)            exp_out = Y5;
        else if (Address==9'h07C)            exp_out = Y6;
        else if (Address==9'h080)            exp_out = Y7;
        else if (Address==9'h084)            exp_out = Y8;
        else if (Address==9'h088)            exp_out = Y9;
        else                                 exp_out = '0;
      end else begin
        exp_out = '0;
      end
    end
  endfunction

  // Assertion: DUT output matches golden model at all times
  always_comb begin
    automatic signed [Width-1:0] exp = exp_out();
    assert (OutDato === exp)
      else $error("EscrituraRegistroToMemoria: OutDato=%0d mismatches expected=%0d at Address=0x%03h (Read=%0b, ListoIn=%0b, InError=%0b)",
                  OutDato, exp, Address, Read, ListoIn, InError);

    // Sanity: outputs known; inputs can be X, but OutDato must never be X/Z
    assert (!$isunknown(OutDato))
      else $error("EscrituraRegistroToMemoria: OutDato has X/Z");

    // Key behaviors (redundant with main assert, but explicit checks for corner gating)
    assert (!Read -> OutDato=='0);
    assert (Read && Address==9'h000 && !ListoIn -> OutDato=='0);
    assert (Read && Address==9'h008 && !InError -> OutDato=='0);
  end

  // Concise, but thorough coverage

  // Cover the two gated constant paths (true/false)
  always_comb begin
    cover (Read && Address==9'h000 &&  ListoIn && OutDato===signed'(1));
    cover (Read && Address==9'h000 && !ListoIn && OutDato==='0);
    cover (Read && Address==9'h008 &&  InError && OutDato===signed'(1));
    cover (Read && Address==9'h008 && !InError && OutDato==='0);
  end

  // Cover all non-gated mapped addresses being accessed at least once
  localparam int unsigned NMAP = 33;
  localparam logic [8:0] MAP_ADDR [NMAP] = '{
    9'h004, // InDato
    9'h00C,9'h010,9'h014,9'h018,9'h01C,9'h020,9'h024,9'h028,9'h02C,9'h030,9'h034,9'h038,9'h03C,
    9'h040,9'h044,9'h048,9'h04C,9'h050,9'h054,9'h058, // Coeff00..Coeff19
    9'h05C, // Offset
    9'h060, // DatoEntradaSistema
    9'h064,9'h068,9'h06C,9'h070,9'h074,9'h078,9'h07C,9'h080,9'h084,9'h088 // Y0..Y9
  };

  genvar i;
  generate
    for (i=0;i<NMAP;i++) begin : g_cov_map
      always_comb cover (Read && Address==MAP_ADDR[i]);
    end
  endgenerate

  // Cover default/unmapped address behavior -> zero
  // Note: includes 0x000 and 0x008 when their gates are false, but we already covered those.
  always_comb begin
    cover (Read &&
           !(Address inside {
             9'h000,9'h004,9'h008,
             9'h00C,9'h010,9'h014,9'h018,9'h01C,9'h020,9'h024,9'h028,9'h02C,9'h030,9'h034,9'h038,9'h03C,
             9'h040,9'h044,9'h048,9'h04C,9'h050,9'h054,9'h058,9'h05C,9'h060,
             9'h064,9'h068,9'h06C,9'h070,9'h074,9'h078,9'h07C,9'h080,9'h084,9'h088
           }) &&
           OutDato==='0);
    cover (!Read && OutDato==='0);
  end

endmodule

bind EscrituraRegistroToMemoria EscrituraRegistroToMemoria_sva #(.Width(Width)) u_escritura_sva (.*);