```systemverilog
module parity_check_sva (
  input logic [7:0] data,
  input logic parity_error
);
  // Parity error should be set when the XOR of the data bits is not zero.
  parity_error_check: assert property (
    @(posedge CLK) disable iff (!RESETn) (parity_error == (^data != 1))
  );
endmodule
```