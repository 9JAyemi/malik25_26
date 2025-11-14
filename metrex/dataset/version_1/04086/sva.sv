// SVA checker for ALU and MyAdder
// Bind these into the DUTs from your testbench

module ALU_sva #(parameter bit COV = 1)
(
  input logic clk,
  input logic rst_n,
  // DUT ports
  input  logic [10:0] OP,
  input  logic [7:0]  A,
  input  logic [7:0]  B,
  input  logic        CI,
  input  logic        CO,
  input  logic        VO,
  input  logic        SO,
  input  logic        ZO,
  input  logic [7:0]  Result,
  input  logic [7:0]  IntR
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Opcodes used by DUT
  localparam logic [10:0]
    OP_ADD = 11'b00_00_00_000,
    OP_SUB = 11'b00_00_00_001,
    OP_AND = 11'b00_00_00_010,
    OP_OR  = 11'b00_00_00_011,
    OP_XOR = 11'b00_00_00_100,
    OP_INC = 11'b00_00_00_101,
    OP_DEC = 11'b00_00_00_110,
    OP_SHL = 11'b00_00_00_111,
    OP_SHR = 11'b00_00_01_000,
    OP_ROL = 11'b00_00_01_001,
    OP_ROR = 11'b00_00_01_010,
    OP_SLT = 11'b00_00_01_011;

  let valid_op = OP inside {OP_ADD,OP_SUB,OP_AND,OP_OR,OP_XOR,OP_INC,OP_DEC,OP_SHL,OP_SHR,OP_ROL,OP_ROR,OP_SLT};

  // Helpers (compute expected values)
  let add_sum9 = {1'b0,A} + {1'b0,B} + CI;
  let sub_sum9 = {1'b0,A} + {1'b0,(~B + 8'd1)} + CI;
  let inc8     = (A + 8'd1) [7:0];
  let dec8     = (A - 8'd1) [7:0];
  let shl8     = (B << 1)   [7:0];
  let shr_b8   = (B >> 1)   [7:0];
  let shr_sum9 = {1'b0,A} + {1'b0,shr_b8} + B[0];
  let rol8     = {B[6:0], B[7]};
  let ror8     = {B[0],   B[7:1]};
  let slt8     = (A < B) ? 8'h01 : 8'h00;

  // Cleanliness: outputs shall not be X/Z when inputs are known
  assert property (!$isunknown({OP,A,B,CI})) |-> !$isunknown({CO,VO,SO,ZO,Result,IntR}));

  // IntR equals Result always (matches DUT behavior)
  assert property (IntR == Result);

  // SO flag equals MSB of Result always (matches DUT behavior)
  assert property (SO == Result[7]);

  // ZO definition for valid ops vs default
  assert property (valid_op |-> (ZO == (Result == 8'h00)));
  assert property (!valid_op |-> (Result==8'h00 && IntR==8'h00 && CO==1'b0 && VO==1'b0 && SO==1'b0 && ZO==1'b0));

  // ADD
  assert property (OP==OP_ADD |-> (
      Result == add_sum9[7:0] &&
      CO     == add_sum9[8]   &&
      VO     == ((A[7]==B[7]) && (Result[7]!=A[7]))
  ));

  // SUB (A + (~B+1) + CI)
  assert property (OP==OP_SUB |-> (
      Result == sub_sum9[7:0] &&
      CO     == sub_sum9[8]   &&
      VO     == ((A[7]!=B[7]) && (Result[7]!=A[7]))
  ));

  // AND
  assert property (OP==OP_AND |-> (
      Result == (A & B) &&
      CO==1'b0 && VO==1'b0
  ));

  // OR
  assert property (OP==OP_OR  |-> (
      Result == (A | B) &&
      CO==1'b0 && VO==1'b0
  ));

  // XOR
  assert property (OP==OP_XOR |-> (
      Result == (A ^ B) &&
      CO==1'b0 && VO==1'b0
  ));

  // INC
  assert property (OP==OP_INC |-> (
      Result == inc8                   &&
      CO     == (A==8'hFF)            &&
      VO     == (A[7]==1'b1 && Result[7]==1'b0)
  ));

  // DEC
  assert property (OP==OP_DEC |-> (
      Result == dec8                   &&
      CO     == (A==8'h00)            &&
      VO     == (A[7]==1'b0 && Result[7]==1'b1)
  ));

  // SHL (uses B<<1; CO/VO depend on A)
  assert property (OP==OP_SHL |-> (
      Result == shl8                  &&
      CO     == A[7]                  &&
      VO     == (A[7] != Result[7])
  ));

  // SHR (Result = A + (B>>1) + B[0]; CO=A[0]; VO=0)
  assert property (OP==OP_SHR |-> (
      Result == shr_sum9[7:0]         &&
      CO     == A[0]                  &&
      VO     == 1'b0
  ));

  // ROL (rotate B; CO=A[7]; VO compares A[7] to Result[7])
  assert property (OP==OP_ROL |-> (
      Result == rol8                  &&
      CO     == A[7]                  &&
      VO     == (A[7] != Result[7])
  ));

  // ROR (rotate B; CO=A[0]; VO compares A[0] to Result[0])
  assert property (OP==OP_ROR |-> (
      Result == ror8                  &&
      CO     == A[0]                  &&
      VO     == (A[0] != Result[0])
  ));

  // SLT
  assert property (OP==OP_SLT |-> (
      Result == slt8                  &&
      CO==1'b0 && VO==1'b0
  ));

  // Functional coverage (optional, controlled by COV)
  if (COV) begin
    cover property (OP==OP_ADD);
    cover property (OP==OP_SUB);
    cover property (OP==OP_AND);
    cover property (OP==OP_OR);
    cover property (OP==OP_XOR);
    cover property (OP==OP_INC);
    cover property (OP==OP_DEC);
    cover property (OP==OP_SHL);
    cover property (OP==OP_SHR);
    cover property (OP==OP_ROL);
    cover property (OP==OP_ROR);
    cover property (OP==OP_SLT);
    // Boundary/corner covers
    cover property (OP==OP_ADD && CO);
    cover property (OP==OP_ADD && VO);
    cover property (OP==OP_SUB && CO);
    cover property (OP==OP_SUB && VO);
    cover property (OP==OP_INC && CO && VO);
    cover property (OP==OP_DEC && CO && VO);
    cover property (OP==OP_SHL && CO && VO);
    cover property (OP==OP_SHR && CO);
    cover property (OP==OP_ROL && VO);
    cover property (OP==OP_ROR && VO);
    cover property (OP==OP_SLT && Result==8'h01);
    cover property (OP==OP_SLT && Result==8'h00);
    cover property (valid_op && ZO && Result==8'h00);
  end

endmodule


module MyAdder_sva
(
  input logic clk,
  input logic rst_n,
  // DUT ports
  input  logic [7:0] A,
  input  logic [7:0] B,
  input  logic       CI,
  input  logic [7:0] S,
  input  logic       CO
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  let sum9 = {1'b0,A} + {1'b0,B} + CI;

  assert property (!$isunknown({A,B,CI})) |-> !$isunknown({S,CO});
  assert property (S == sum9[7:0] && CO == sum9[8]);

  // Coverage
  cover property (CO);
  cover property (S==8'h00);
  cover property (S==8'hFF);
endmodule


// Example bind statements (adjust clock/reset handles as appropriate)
// bind ALU     ALU_sva     u_alu_sva     (.clk(tb_clk), .rst_n(tb_rst_n), .*);
// bind MyAdder MyAdder_sva u_myadder_sva (.clk(tb_clk), .rst_n(tb_rst_n), .*);