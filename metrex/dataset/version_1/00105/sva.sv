// SVA for RegistroWithMuxInput
// Bind this module to the DUT. Focused, concise checks + coverage.

module RegistroWithMuxInput_sva #(parameter Width=4) (
  input  logic                          CLK,
  input  logic                          reset,
  input  logic                          EnableRegisterIn,
  input  logic [3:0]                    SELCoeffX,
  input  logic [3:0]                    SELCoeffY,

  input  logic signed [Width-1:0]       Coeff00,Coeff01,Coeff02,Coeff03,Coeff04,
                                        Coeff05,Coeff06,Coeff07,Coeff08,Coeff09,
                                        Coeff10,Coeff11,Coeff12,Coeff13,Coeff14,
                                        Coeff15,Coeff16,Coeff17,Coeff18,Coeff19,
                                        OffsetIn,

  input  logic signed [Width-1:0]       OutCoeffX,
  input  logic signed [Width-1:0]       OutCoeffY,
  input  logic signed [Width-1:0]       OffsetOut,

  input  logic signed [Width-1:0]       AuxCoeff00,AuxCoeff01,AuxCoeff02,AuxCoeff03,AuxCoeff04,
                                        AuxCoeff05,AuxCoeff06,AuxCoeff07,AuxCoeff08,AuxCoeff09,
                                        AuxCoeff10,AuxCoeff11,AuxCoeff12,AuxCoeff13,AuxCoeff14,
                                        AuxCoeff15,AuxCoeff16,AuxCoeff17,AuxCoeff18,AuxCoeff19,
                                        AuxCoeff20
);

  default clocking cb @(posedge CLK); endclocking

  // Reset clears all storage
  assert property (reset |=> {AuxCoeff00,AuxCoeff01,AuxCoeff02,AuxCoeff03,AuxCoeff04,
                              AuxCoeff05,AuxCoeff06,AuxCoeff07,AuxCoeff08,AuxCoeff09,
                              AuxCoeff10,AuxCoeff11,AuxCoeff12,AuxCoeff13,AuxCoeff14,
                              AuxCoeff15,AuxCoeff16,AuxCoeff17,AuxCoeff18,AuxCoeff19,
                              AuxCoeff20} == '0);

  // Enable loads inputs (incl. OffsetIn -> AuxCoeff20)
  assert property (!reset && EnableRegisterIn |=> 
                  {AuxCoeff00,AuxCoeff01,AuxCoeff02,AuxCoeff03,AuxCoeff04,
                   AuxCoeff05,AuxCoeff06,AuxCoeff07,AuxCoeff08,AuxCoeff09,
                   AuxCoeff10,AuxCoeff11,AuxCoeff12,AuxCoeff13,AuxCoeff14,
                   AuxCoeff15,AuxCoeff16,AuxCoeff17,AuxCoeff18,AuxCoeff19,
                   AuxCoeff20}
                   == $past({Coeff00,Coeff01,Coeff02,Coeff03,Coeff04,
                            Coeff05,Coeff06,Coeff07,Coeff08,Coeff09,
                            Coeff10,Coeff11,Coeff12,Coeff13,Coeff14,
                            Coeff15,Coeff16,Coeff17,Coeff18,Coeff19,
                            OffsetIn})));

  // Hold when not enabled
  assert property (!reset && !EnableRegisterIn |=> 
                  {AuxCoeff00,AuxCoeff01,AuxCoeff02,AuxCoeff03,AuxCoeff04,
                   AuxCoeff05,AuxCoeff06,AuxCoeff07,AuxCoeff08,AuxCoeff09,
                   AuxCoeff10,AuxCoeff11,AuxCoeff12,AuxCoeff13,AuxCoeff14,
                   AuxCoeff15,AuxCoeff16,AuxCoeff17,AuxCoeff18,AuxCoeff19,
                   AuxCoeff20}
                   == $past({AuxCoeff00,AuxCoeff01,AuxCoeff02,AuxCoeff03,AuxCoeff04,
                             AuxCoeff05,AuxCoeff06,AuxCoeff07,AuxCoeff08,AuxCoeff09,
                             AuxCoeff10,AuxCoeff11,AuxCoeff12,AuxCoeff13,AuxCoeff14,
                             AuxCoeff15,AuxCoeff16,AuxCoeff17,AuxCoeff18,AuxCoeff19,
                             AuxCoeff20})));

  // OffsetOut mirrors AuxCoeff20
  assert property (1 |-> OffsetOut == AuxCoeff20);

  // Mux correctness X (0..9) and default
  assert property (SELCoeffX==4'd0  |-> OutCoeffX==AuxCoeff00);
  assert property (SELCoeffX==4'd1  |-> OutCoeffX==AuxCoeff01);
  assert property (SELCoeffX==4'd2  |-> OutCoeffX==AuxCoeff02);
  assert property (SELCoeffX==4'd3  |-> OutCoeffX==AuxCoeff03);
  assert property (SELCoeffX==4'd4  |-> OutCoeffX==AuxCoeff04);
  assert property (SELCoeffX==4'd5  |-> OutCoeffX==AuxCoeff05);
  assert property (SELCoeffX==4'd6  |-> OutCoeffX==AuxCoeff06);
  assert property (SELCoeffX==4'd7  |-> OutCoeffX==AuxCoeff07);
  assert property (SELCoeffX==4'd8  |-> OutCoeffX==AuxCoeff08);
  assert property (SELCoeffX==4'd9  |-> OutCoeffX==AuxCoeff09);
  assert property (!$isunknown(SELCoeffX) && (SELCoeffX>=4'd10) |-> OutCoeffX=='0);

  // Mux correctness Y (0..9 -> AuxCoeff10..19) and default
  assert property (SELCoeffY==4'd0  |-> OutCoeffY==AuxCoeff10);
  assert property (SELCoeffY==4'd1  |-> OutCoeffY==AuxCoeff11);
  assert property (SELCoeffY==4'd2  |-> OutCoeffY==AuxCoeff12);
  assert property (SELCoeffY==4'd3  |-> OutCoeffY==AuxCoeff13);
  assert property (SELCoeffY==4'd4  |-> OutCoeffY==AuxCoeff14);
  assert property (SELCoeffY==4'd5  |-> OutCoeffY==AuxCoeff15);
  assert property (SELCoeffY==4'd6  |-> OutCoeffY==AuxCoeff16);
  assert property (SELCoeffY==4'd7  |-> OutCoeffY==AuxCoeff17);
  assert property (SELCoeffY==4'd8  |-> OutCoeffY==AuxCoeff18);
  assert property (SELCoeffY==4'd9  |-> OutCoeffY==AuxCoeff19);
  assert property (!$isunknown(SELCoeffY) && (SELCoeffY>=4'd10) |-> OutCoeffY=='0);

  // Outputs never X/Z at sampling
  assert property (!$isunknown({OutCoeffX,OutCoeffY,OffsetOut}));

  // Coverage
  cover property (reset);
  cover property (!reset && EnableRegisterIn);
  cover property (SELCoeffX inside {4'd0,4'd1,4'd2,4'd3,4'd4,4'd5,4'd6,4'd7,4'd8,4'd9});
  cover property (SELCoeffY inside {4'd0,4'd1,4'd2,4'd3,4'd4,4'd5,4'd6,4'd7,4'd8,4'd9});
  cover property (!reset && SELCoeffX>=4'd10);
  cover property (!reset && SELCoeffY>=4'd10);

endmodule

// Bind into the DUT
bind RegistroWithMuxInput
  RegistroWithMuxInput_sva #(.Width(Width)) u_reg_with_mux_sva (
    .CLK(CLK),
    .reset(reset),
    .EnableRegisterIn(EnableRegisterIn),
    .SELCoeffX(SELCoeffX),
    .SELCoeffY(SELCoeffY),
    .Coeff00(Coeff00), .Coeff01(Coeff01), .Coeff02(Coeff02), .Coeff03(Coeff03), .Coeff04(Coeff04),
    .Coeff05(Coeff05), .Coeff06(Coeff06), .Coeff07(Coeff07), .Coeff08(Coeff08), .Coeff09(Coeff09),
    .Coeff10(Coeff10), .Coeff11(Coeff11), .Coeff12(Coeff12), .Coeff13(Coeff13), .Coeff14(Coeff14),
    .Coeff15(Coeff15), .Coeff16(Coeff16), .Coeff17(Coeff17), .Coeff18(Coeff18), .Coeff19(Coeff19),
    .OffsetIn(OffsetIn),
    .OutCoeffX(OutCoeffX),
    .OutCoeffY(OutCoeffY),
    .OffsetOut(OffsetOut),
    .AuxCoeff00(AuxCoeff00), .AuxCoeff01(AuxCoeff01), .AuxCoeff02(AuxCoeff02), .AuxCoeff03(AuxCoeff03), .AuxCoeff04(AuxCoeff04),
    .AuxCoeff05(AuxCoeff05), .AuxCoeff06(AuxCoeff06), .AuxCoeff07(AuxCoeff07), .AuxCoeff08(AuxCoeff08), .AuxCoeff09(AuxCoeff09),
    .AuxCoeff10(AuxCoeff10), .AuxCoeff11(AuxCoeff11), .AuxCoeff12(AuxCoeff12), .AuxCoeff13(AuxCoeff13), .AuxCoeff14(AuxCoeff14),
    .AuxCoeff15(AuxCoeff15), .AuxCoeff16(AuxCoeff16), .AuxCoeff17(AuxCoeff17), .AuxCoeff18(AuxCoeff18), .AuxCoeff19(AuxCoeff19),
    .AuxCoeff20(AuxCoeff20)
  );