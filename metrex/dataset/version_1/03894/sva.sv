// SVA checker for tri_intersect_data_array
// Binds a cycle-accurate reference model and assertions that
// verify address legality, write semantics/priorities, and q0/q1 correctness.

module tri_intersect_data_array_sva #(
  parameter int DataWidth    = 576,
  parameter int AddressRange = 20,
  parameter int AddressWidth = 5
)(
  input  logic                       reset,
  input  logic                       clk,
  input  logic [AddressWidth-1:0]    address0,
  input  logic                       ce0,
  input  logic                       we0,
  input  logic [DataWidth-1:0]       d0,
  input  logic [DataWidth-1:0]       q0,
  input  logic [AddressWidth-1:0]    address1,
  input  logic                       ce1,
  input  logic                       we1,
  input  logic [DataWidth-1:0]       d1,
  input  logic [DataWidth-1:0]       q1
);

  // Lightweight golden model of the internal array with identical reset/priority semantics
  logic [DataWidth-1:0] mem_ref [0:AddressRange-1];

  // Asynchronous reset, single-write-per-cycle with port0 priority
  integer i;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      for (i = 0; i < AddressRange; i++) mem_ref[i] <= '0;
    end else if (ce0 && we0) begin
      mem_ref[address0] <= d0;
    end else if (ce1 && we1) begin
      mem_ref[address1] <= d1;
    end
  end

  // Basic hygiene
  // Addresses must be in range (prevents out-of-bounds/X indexing)
  assert property (@(posedge clk) disable iff (reset)
                   (address0 < AddressRange) && (address1 < AddressRange))
    else $error("Address out of range");

  // Optional protocol sanity: writes imply chip-enable
  assert property (@(posedge clk) disable iff (reset) we0 |-> ce0)
    else $error("we0 asserted without ce0");
  assert property (@(posedge clk) disable iff (reset) we1 |-> ce1)
    else $error("we1 asserted without ce1");

  // Outputs are always identical by construction
  assert property (@(posedge clk) q0 == q1)
    else $error("q0 != q1");

  // Functional correctness: q equals ref_mem[address0] & ref_mem[address1]
  assert property (@(posedge clk) disable iff (reset)
                   q0 == (mem_ref[address0] & mem_ref[address1]))
    else $error("q mismatch vs reference model");

  // No X/Z on observable outputs (after reset)
  assert property (@(posedge clk) disable iff (reset)
                   !$isunknown(q0) && !$isunknown(q1))
    else $error("Unknown detected on q outputs");

  // Coverage: reset, writes, priority, address corners, data activity
  cover property (@(posedge clk) reset);
  cover property (@(posedge clk) disable iff (reset) (ce0 && we0) && !(ce1 && we1));         // port0-only write
  cover property (@(posedge clk) disable iff (reset) (ce1 && we1) && !(ce0 && we0));         // port1-only write
  cover property (@(posedge clk) disable iff (reset) (ce0 && we0) && (ce1 && we1));          // simultaneous writes (priority case)
  cover property (@(posedge clk) disable iff (reset) (ce0 && we0) && (address0 == '0));      // write to first address
  cover property (@(posedge clk) disable iff (reset) (ce1 && we1) && (address1 == AddressRange-1)); // write to last address
  cover property (@(posedge clk) disable iff (reset) q0 == '0);                               // zero result observation
  cover property (@(posedge clk) disable iff (reset) q0 != '0);                               // non-zero result observation

endmodule

// Bind the checker to the DUT
bind tri_intersect_data_array
  tri_intersect_data_array_sva #(
    .DataWidth(DataWidth),
    .AddressRange(AddressRange),
    .AddressWidth(AddressWidth)
  ) tri_intersect_data_array_sva_i (
    .reset,
    .clk,
    .address0,
    .ce0,
    .we0,
    .d0,
    .q0,
    .address1,
    .ce1,
    .we1,
    .d1,
    .q1
  );