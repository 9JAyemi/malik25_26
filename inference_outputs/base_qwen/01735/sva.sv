```systemverilog
module tri_buf_sva (
    inout wire A,
    output wire Z,
    input wire TE_B
);
    // TE_B can only transition from LOW to HIGH when A is LOW.
    tri_buf_1: assert property (
        @(posedge TE_B) $rose(TE_B) |-> (A == 1'b0)
    );
    // TE_B can only transition from HIGH to LOW when Z is LOW.
    tri_buf_2: assert property (
        @(posedge TE_B) $fell(TE_B) |-> (Z == 1'b0)
    );
    // Z can only transition from LOW to HIGH when TE_B is HIGH.
    tri_buf_3: assert property (
        @(posedge TE_B) $rose(Z) |-> (TE_B == 1'b1)
    );
    // Z can only transition from HIGH to LOW when TE_B is LOW.
    tri_buf_4: assert property (
        @(posedge TE_B) $fell(Z) |-> (TE_B == 1'b0)
    );
    // A can only transition from LOW to HIGH when TE_B is HIGH.
    tri_buf_5: assert property (
        @(posedge TE_B) $rose(A) |-> (TE_B == 1'b1)
    );
    // A can only transition from HIGH to LOW when TE_B is LOW.
    tri_buf_6: assert property (
        @(posedge TE_B) $fell(A) |-> (TE_B == 1'b0)
    );
endmodule
```