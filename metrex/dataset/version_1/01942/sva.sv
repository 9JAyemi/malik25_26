// SVA checker for HAZARD_CONTROL_UNIT
// Bind this module to the DUT; provide a sampling clk and an optional active-low reset.
// If no reset is available, tie rst_n to 1'b1.

module HAZARD_CONTROL_UNIT_sva #(
  parameter REG_ADD_WIDTH        = 5,
  parameter D_CACHE_LW_WIDTH     = 3,
  parameter DATA_CACHE_LOAD_NONE = 3'b000
)(
  input  logic                                clk,
  input  logic                                rst_n,

  // DUT inputs
  input  logic                                INSTRUCTION_CACHE_READY,
  input  logic                                DATA_CACHE_READY,     // unused in DUT
  input  logic                                PC_MISPREDICTED,
  input  logic [REG_ADD_WIDTH-1:0]            RS1_ADDRESS_EXECUTION,
  input  logic [REG_ADD_WIDTH-1:0]            RS2_ADDRESS_EXECUTION,
  input  logic [D_CACHE_LW_WIDTH-1:0]         DATA_CACHE_LOAD_DM1,
  input  logic [REG_ADD_WIDTH-1:0]            RD_ADDRESS_DM1,
  input  logic [D_CACHE_LW_WIDTH-1:0]         DATA_CACHE_LOAD_DM2,
  input  logic [REG_ADD_WIDTH-1:0]            RD_ADDRESS_DM2,
  input  logic [D_CACHE_LW_WIDTH-1:0]         DATA_CACHE_LOAD_DM3,
  input  logic [REG_ADD_WIDTH-1:0]            RD_ADDRESS_DM3,

  // DUT outputs
  input  logic                                CLEAR_INSTRUCTION_FETCH_STAGE,
  input  logic                                CLEAR_DECODING_STAGE,
  input  logic                                CLEAR_EXECUTION_STAGE,
  input  logic                                STALL_PROGRAME_COUNTER_STAGE,
  input  logic                                STALL_INSTRUCTION_CACHE,
  input  logic                                STALL_INSTRUCTION_FETCH_STAGE,
  input  logic                                STALL_DECODING_STAGE,
  input  logic                                STALL_EXECUTION_STAGE,
  input  logic                                STALL_DATA_MEMORY_STAGE
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  function automatic logic hazard_det;
    hazard_det =
      ( ((RS1_ADDRESS_EXECUTION==RD_ADDRESS_DM1) || (RS2_ADDRESS_EXECUTION==RD_ADDRESS_DM1)) &&
        (DATA_CACHE_LOAD_DM1 != DATA_CACHE_LOAD_NONE) ) ||
      ( ((RS1_ADDRESS_EXECUTION==RD_ADDRESS_DM2) || (RS2_ADDRESS_EXECUTION==RD_ADDRESS_DM2)) &&
        (DATA_CACHE_LOAD_DM2 != DATA_CACHE_LOAD_NONE) ) ||
      ( ((RS1_ADDRESS_EXECUTION==RD_ADDRESS_DM3) || (RS2_ADDRESS_EXECUTION==RD_ADDRESS_DM3)) &&
        (DATA_CACHE_LOAD_DM3 != DATA_CACHE_LOAD_NONE) );
  endfunction

  // No-X on outputs when inputs are known
  assert property ( !$isunknown({
                        INSTRUCTION_CACHE_READY, PC_MISPREDICTED,
                        RS1_ADDRESS_EXECUTION, RS2_ADDRESS_EXECUTION,
                        DATA_CACHE_LOAD_DM1, RD_ADDRESS_DM1,
                        DATA_CACHE_LOAD_DM2, RD_ADDRESS_DM2,
                        DATA_CACHE_LOAD_DM3, RD_ADDRESS_DM3
                      })
                    |-> !$isunknown({
                        CLEAR_INSTRUCTION_FETCH_STAGE, CLEAR_DECODING_STAGE, CLEAR_EXECUTION_STAGE,
                        STALL_PROGRAME_COUNTER_STAGE, STALL_INSTRUCTION_CACHE, STALL_INSTRUCTION_FETCH_STAGE,
                        STALL_DECODING_STAGE, STALL_EXECUTION_STAGE, STALL_DATA_MEMORY_STAGE
                      }) );

  // Canonical combinational mapping checks
  assert property ( CLEAR_INSTRUCTION_FETCH_STAGE == PC_MISPREDICTED );
  assert property ( CLEAR_DECODING_STAGE == ( (!hazard_det()) && ((!INSTRUCTION_CACHE_READY) || PC_MISPREDICTED) ) );
  assert property ( CLEAR_EXECUTION_STAGE == hazard_det() );

  assert property ( STALL_PROGRAME_COUNTER_STAGE   == ( hazard_det() || !INSTRUCTION_CACHE_READY ) );
  assert property ( STALL_INSTRUCTION_CACHE        ==   hazard_det() );
  assert property ( STALL_INSTRUCTION_FETCH_STAGE  == ( hazard_det() || !INSTRUCTION_CACHE_READY ) );
  assert property ( STALL_DECODING_STAGE           == ( hazard_det() || !INSTRUCTION_CACHE_READY ) );
  assert property ( STALL_EXECUTION_STAGE          ==   hazard_det() );

  // Output is never driven in RTL: must remain 0
  assert property ( STALL_DATA_MEMORY_STAGE == 1'b0 );

  // Scenario coverage
  cover property ( hazard_det() );                                           // any hazard
  cover property ( !hazard_det() && !INSTRUCTION_CACHE_READY );              // icache wait only
  cover property ( !hazard_det() &&  INSTRUCTION_CACHE_READY && PC_MISPREDICTED ); // mispredict only
  cover property ( !hazard_det() &&  INSTRUCTION_CACHE_READY && !PC_MISPREDICTED ); // clean flow
  cover property ( hazard_det() && PC_MISPREDICTED );                        // hazard + mispredict
  cover property ( hazard_det() && !INSTRUCTION_CACHE_READY );               // hazard + icache wait (hazard dominates)

  // Per-stage hazard contributors
  cover property ( ((RS1_ADDRESS_EXECUTION==RD_ADDRESS_DM1)||(RS2_ADDRESS_EXECUTION==RD_ADDRESS_DM1)) &&
                   (DATA_CACHE_LOAD_DM1 != DATA_CACHE_LOAD_NONE) );
  cover property ( ((RS1_ADDRESS_EXECUTION==RD_ADDRESS_DM2)||(RS2_ADDRESS_EXECUTION==RD_ADDRESS_DM2)) &&
                   (DATA_CACHE_LOAD_DM2 != DATA_CACHE_LOAD_NONE) );
  cover property ( ((RS1_ADDRESS_EXECUTION==RD_ADDRESS_DM3)||(RS2_ADDRESS_EXECUTION==RD_ADDRESS_DM3)) &&
                   (DATA_CACHE_LOAD_DM3 != DATA_CACHE_LOAD_NONE) );

endmodule

// Example bind (adjust clk/rst as appropriate):
// bind HAZARD_CONTROL_UNIT HAZARD_CONTROL_UNIT_sva #(
//   .REG_ADD_WIDTH(REG_ADD_WIDTH),
//   .D_CACHE_LW_WIDTH(D_CACHE_LW_WIDTH),
//   .DATA_CACHE_LOAD_NONE(DATA_CACHE_LOAD_NONE)
// ) u_hcu_sva (
//   .clk(tb_clk),
//   .rst_n(tb_rst_n),
//   .INSTRUCTION_CACHE_READY(INSTRUCTION_CACHE_READY),
//   .DATA_CACHE_READY(DATA_CACHE_READY),
//   .PC_MISPREDICTED(PC_MISPREDICTED),
//   .RS1_ADDRESS_EXECUTION(RS1_ADDRESS_EXECUTION),
//   .RS2_ADDRESS_EXECUTION(RS2_ADDRESS_EXECUTION),
//   .DATA_CACHE_LOAD_DM1(DATA_CACHE_LOAD_DM1),
//   .RD_ADDRESS_DM1(RD_ADDRESS_DM1),
//   .DATA_CACHE_LOAD_DM2(DATA_CACHE_LOAD_DM2),
//   .RD_ADDRESS_DM2(RD_ADDRESS_DM2),
//   .DATA_CACHE_LOAD_DM3(DATA_CACHE_LOAD_DM3),
//   .RD_ADDRESS_DM3(RD_ADDRESS_DM3),
//   .CLEAR_INSTRUCTION_FETCH_STAGE(CLEAR_INSTRUCTION_FETCH_STAGE),
//   .CLEAR_DECODING_STAGE(CLEAR_DECODING_STAGE),
//   .CLEAR_EXECUTION_STAGE(CLEAR_EXECUTION_STAGE),
//   .STALL_PROGRAME_COUNTER_STAGE(STALL_PROGRAME_COUNTER_STAGE),
//   .STALL_INSTRUCTION_CACHE(STALL_INSTRUCTION_CACHE),
//   .STALL_INSTRUCTION_FETCH_STAGE(STALL_INSTRUCTION_FETCH_STAGE),
//   .STALL_DECODING_STAGE(STALL_DECODING_STAGE),
//   .STALL_EXECUTION_STAGE(STALL_EXECUTION_STAGE),
//   .STALL_DATA_MEMORY_STAGE(STALL_DATA_MEMORY_STAGE)
// );