// SVA checker for soc_design_SystemID
module soc_design_SystemID_sva (
  input  logic        clock,
  input  logic        reset_n,
  input  logic [31:0] address,
  input  logic [31:0] readdata
);
  default clocking cb @(posedge clock); endclocking

  localparam logic [31:0] A0 = 32'h0000_0000;
  localparam logic [31:0] A4 = 32'h0000_0004;
  localparam logic [31:0] D0 = 32'hDEAD_BEEF;
  localparam logic [31:0] D4 = 32'hCAFE_BABE;
  localparam logic [31:0] DZ = 32'h0000_0000;

  function automatic logic [31:0] exp_data(input logic [31:0] a);
    case (a)
      A0:     exp_data = D0;
      A4:     exp_data = D4;
      default:exp_data = DZ;
    endcase
  endfunction

  // Reset drives zero next cycle and while held
  assert property (!reset_n |=> readdata == DZ);
  assert property ($past(!reset_n) && !reset_n |-> readdata == DZ);

  // Functional mapping: 1-cycle latency from address to readdata when not in reset
  assert property ($past(reset_n) |-> readdata == exp_data($past(address)));

  // Sanity: only legal constant values when out of reset
  assert property (reset_n |-> (readdata == DZ || readdata == D0 || readdata == D4));

  // Coverage: exercise all address cases and reset release
  cover property (!reset_n ##1 reset_n);                                  // reset release
  cover property (reset_n && address == A0 ##1 readdata == D0);           // addr 0 -> DEADBEEF
  cover property (reset_n && address == A4 ##1 readdata == D4);           // addr 4 -> CAFEBABE
  cover property (reset_n && address != A0 && address != A4
                  ##1 readdata == DZ);                                    // default -> 0
  cover property (reset_n && address == A0 ##1 address == A4
                  ##1 readdata == D4);                                    // switch 0 -> 4
endmodule

// Bind into DUT
bind soc_design_SystemID soc_design_SystemID_sva sva_i (
  .clock    (clock),
  .reset_n  (reset_n),
  .address  (address),
  .readdata (readdata)
);