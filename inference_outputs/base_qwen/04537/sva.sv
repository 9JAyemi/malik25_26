```systemverilog
module EtherCAT_slave_sva (
    input logic clk,
    input logic rst,
    input logic [n-1:0] in_receive,
    output logic [n-1:0] out_send
);
    // At reset, out_send should be driven to 0
    reset: assert property (
        @(posedge clk) disable iff (!rst) out_send == 0
    );

    // out_send should always be equal to in_receive
    data_transfer: assert property (
        @(posedge clk) disable iff (!rst) out_send == in_receive
    );
endmodule
```