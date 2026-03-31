```systemverilog
module parity_checker_sva (
  input logic clk,
  input logic rst_n,
  input logic [7:0] data_in,
  input logic sel_b1,
  output logic parity
);
  // Parity calculation is combinational logic, but we use @(posedge clk) for assertions.
  // Parity should be updated on every clock edge.
  parity_update: assert property (
    @(posedge clk) disable iff (!rst_n) (parity == (sel_b1 ? ~data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7] : data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7]))
  );
  // Parity should be stable after reset.
  parity_stable_after_reset: assert property (
    @(posedge clk) disable iff (!rst_n) (rst_n |-> parity == (sel_b1 ? ~data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7] : data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7]))
  );
endmodule
```