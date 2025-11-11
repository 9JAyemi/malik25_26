// SVA for encryption_module
module encryption_module_sva (
  input logic        aclk,
  input logic        reset,
  input logic [15:0] data_in,
  input logic [15:0] data_out,
  input logic [7:0]  A,
  input logic [7:0]  B,
  input logic [7:0]  rotated_A,
  input logic [15:0] result
);
  default clocking cb @(posedge aclk); endclocking

  // Age counter to gate deep $past
  logic [2:0] age;
  always_ff @(posedge aclk) begin
    if (reset) age <= '0;
    else if (age != 3'd7) age <= age + 3'd1;
  end

  // Reset behavior (synchronous)
  assert property (reset |-> (A==8'h00 && B==8'h00 && rotated_A==8'h00 && result==16'h0000 && data_out==16'h0000));

  // Stage-by-stage pipeline checks
  assert property (disable iff (reset) A == $past(data_in[15:8], 1, reset));
  assert property (disable iff (reset) B == $past(data_in[7:0],  1, reset));

  // Rotation: rotated_A uses prior A and rotates right by 2 (left by 6)
  assert property (disable iff (reset) rotated_A == { $past(A,1,reset)[5:0], $past(A,1,reset)[7:6] });

  // 8-bit add, truncated, zero-extended into 16-bit result
  assert property (disable iff (reset) result[7:0]  == ($past(rotated_A,1,reset) + $past(B,1,reset)));
  assert property (disable iff (reset) result[15:8] == 8'h00);

  // Output equals prior result
  assert property (disable iff (reset) data_out == $past(result, 1, reset));

  // End-to-end functional alignment (accounts for pipeline latency/misalignment)
  assert property (disable iff (reset || age < 4)
    data_out == {8'h00, ( { $past(data_in[15:8],4,reset)[5:0], $past(data_in[15:8],4,reset)[7:6] }
                           +  $past(data_in[7:0],3,reset) )});

  // No X/Z after reset deassert
  assert property (disable iff (reset) !$isunknown({A,B,rotated_A,result,data_out}));

  // Coverage
  // - See a nonzero output after pipeline fills
  cover property (disable iff (reset) age>=4 ##1 data_out != 16'h0000);
  // - Exercise 8-bit addition overflow (carry out)
  cover property (disable iff (reset) ({1'b0,$past(rotated_A,1,reset)} + {1'b0,$past(B,1,reset)})[8]);
  // - Observe rotation moving bits [7:6] into [1:0]
  cover property (disable iff (reset) ($past(A,1,reset)[7:6] != 2'b00) && (rotated_A[1:0] == $past(A,1,reset)[7:6]));
endmodule

bind encryption_module encryption_module_sva sva_encryption_module (.*);