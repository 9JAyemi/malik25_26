```systemverilog
module rotation_module_sva (
  input logic clk,
  input logic reset,
  input logic [3:0] in,
  input logic load,
  input logic select,
  input logic [15:0] data,
  output logic [3:0] out
);

  // Reset behavior: out should be 0 at reset
  reset_behavior: assert property (
    @(posedge clk) disable iff (!reset) out == 4'b0
  );

  // Load behavior: out should be the lower 4 bits of data when load is high
  load_behavior: assert property (
    @(posedge clk) disable iff (!reset) (load |-> out == data[3:0])
  );

  // Select behavior: out should be {in[2:0], in[3]} when select is high
  select_behavior: assert property (
    @(posedge clk) disable iff (!reset) (select |-> out == {in[2:0], in[3]})
  );

  // Default behavior: out should be {in[0], in[3:1]} when neither load nor select is high
  default_behavior: assert property (
    @(posedge clk) disable iff (!reset) (!(load | select) |-> out == {in[0], in[3:1]})
  );

endmodule
```