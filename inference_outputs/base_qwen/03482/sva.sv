```systemverilog
module TLU_assertions (
    input logic EN,
    input logic SE,
    input logic CK,
    output logic Q
);
    // EN must be HIGH for Q to be updated
    update_q: assert property (
        @(posedge CK) disable iff (!EN) Q == Q
    );

    // Q should only change when EN is HIGH
    q_change: assert property (
        @(posedge CK) disable iff (!EN) $stable(Q)
    );

    // Q should be equal to SE when EN is HIGH
    q_equal_se: assert property (
        @(posedge CK) disable iff (!EN) (EN == 1'b1) |-> (Q == SE)
    );

    // Q should be 0 when EN is LOW
    q_zero_when_en_low: assert property (
        @(posedge CK) disable iff (EN) Q == 1'b0
    );
endmodule
```