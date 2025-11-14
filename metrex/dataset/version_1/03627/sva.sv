// SVA for acciones_to_bcd
// Focused on correctness after reset (ignores reset-time #delays)

module acciones_to_bcd_sva
(
  input logic        clk,
  input logic        rst,
  input logic [1:0]  piso,
  input logic [1:0]  accion,
  input logic        puertas,
  input logic [3:0]  BCD1,
  input logic [3:0]  BCD2,
  input logic [3:0]  BCD3,
  input logic [3:0]  BCD4
);

  default clocking cb @(posedge clk); endclocking
  // Ignore assertions during reset due to #delays in DUT
  default disable iff (rst);

  // Golden models
  function automatic logic [3:0] piso_to_bcd4 (input logic [1:0] x);
    case (x)
      2'b00: piso_to_bcd4 = 4'b0001;
      2'b01: piso_to_bcd4 = 4'b0010;
      2'b10: piso_to_bcd4 = 4'b0011;
      default: piso_to_bcd4 = 4'b0100;
    endcase
  endfunction

  function automatic logic [3:0] accion_to_bcd1 (input logic [1:0] x);
    case (x)
      2'b00: accion_to_bcd1 = 4'b0000;
      2'b01: accion_to_bcd1 = 4'b0101;
      2'b10: accion_to_bcd1 = 4'b1000;
      default: accion_to_bcd1 = 4'b0000;
    endcase
  endfunction

  // Functional checks (post-reset)
  assert property (BCD4 == piso_to_bcd4(piso));
  assert property (BCD1 == accion_to_bcd1(accion));
  assert property (BCD2 == (puertas ? 4'b0110 : 4'b0111));
  assert property (BCD3 == 4'b1001);

  // Output code validity and no X/Z (post-reset)
  assert property (!$isunknown({piso, accion, puertas}));
  assert property (!$isunknown({BCD1, BCD2, BCD3, BCD4}));
  assert property (BCD4 inside {4'b0001,4'b0010,4'b0011,4'b0100});
  assert property (BCD1 inside {4'b0000,4'b0101,4'b1000});
  assert property (BCD2 inside {4'b0110,4'b0111});
  assert property (BCD3 == 4'b1001);

  // BCD3 must remain stable post-reset
  assert property ($stable(BCD3));

  // Post-reset settle: first cycle after rst deassert -> all fields correct
  // Note: this property purposely not disabled by reset
  assert property (@(posedge clk)
                   $fell(rst) |-> (BCD4 == piso_to_bcd4(piso)
                                   && BCD1 == accion_to_bcd1(accion)
                                   && BCD2 == (puertas ? 4'b0110 : 4'b0111)
                                   && BCD3 == 4'b1001));

  // Coverage
  cover property (piso==2'b00 && BCD4==4'b0001);
  cover property (piso==2'b01 && BCD4==4'b0010);
  cover property (piso==2'b10 && BCD4==4'b0011);
  cover property (piso==2'b11 && BCD4==4'b0100);

  cover property (accion==2'b00 && BCD1==4'b0000);
  cover property (accion==2'b01 && BCD1==4'b0101);
  cover property (accion==2'b10 && BCD1==4'b1000);
  cover property (accion==2'b11 && BCD1==4'b0000);

  cover property (puertas==1'b0 && BCD2==4'b0111);
  cover property (puertas==1'b1 && BCD2==4'b0110);

  // Full cross coverage of inputs with matching outputs
  genvar i,j,k;
  generate
    for (i=0; i<4; i++) begin : C_PISO
      localparam logic [1:0] PI = i[1:0];
      for (j=0; j<4; j++) begin : C_ACC
        localparam logic [1:0] AJ = j[1:0];
        for (k=0; k<2; k++) begin : C_PUERTAS
          localparam logic PK = k[0:0];
          cover property (piso==PI && accion==AJ && puertas==PK
                          && BCD4==piso_to_bcd4(PI)
                          && BCD1==accion_to_bcd1(AJ)
                          && BCD2==(PK ? 4'b0110 : 4'b0111)
                          && BCD3==4'b1001);
        end
      end
    end
  endgenerate

endmodule

// Bind into DUT
bind acciones_to_bcd acciones_to_bcd_sva sva_i (.*);