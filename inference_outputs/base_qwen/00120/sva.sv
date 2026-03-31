```systemverilog
module sky130_fd_sc_ms__a2111oi_sva (
    input logic Y   ,
    input logic A1  ,
    input logic A2  ,
    input logic B1  ,
    input logic C1  ,
    input logic D1  ,
    input logic VPWR,
    input logic VGND,
    input logic VPB ,
    input logic VNB
);
    // The logic is purely combinational as it only uses input signals and produces an output.

    // The output Y is a function of the inputs A1, A2, B1, C1, and D1.
    // It is always high if any combination of the inputs is true.
    // It is always low if all inputs are false.

    // Combinational logic assertion
    // Y is high if any combination of A1, A2, B1, C1, and D1 is true.
    combinational_logic: assert property (
        @(posedge VPWR) disable iff (!VGND) (Y == 1'b1) |-> (A1 | A2 | B1 | C1 | D1)
    );

    // Combinational logic assertion
    // Y is low if all inputs are false.
    combinational_logic_2: assert property (
        @(posedge VPWR) disable iff (!VGND) (Y == 1'b0) |-> (!A1 & !A2 & !B1 & !C1 & !D1)
    );
endmodule
```