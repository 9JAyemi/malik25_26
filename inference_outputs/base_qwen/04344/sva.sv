```systemverilog
module digital_circuit_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // The logic is purely combinational as there are no sequential elements.
    
    // Y is driven by a combination of A1, A2, VPWR, VGND, VPB, and VNB.
    // Y is LOW if any of the following conditions are met:
    // 1. A1 AND A2 are both LOW
    // 2. VPWR is HIGH, VGND is LOW, A1 is LOW, and A2 is HIGH
    // 3. VPWR is LOW, VGND is HIGH, A1 is HIGH, and A2 is LOW
    // Y is also LOW if B1_N is HIGH or if both VGND and VPB and VNB are HIGH.
    // Y is HIGH otherwise.
    
    // Y is LOW when A1 and A2 are both LOW.
    combinational_1: assert property (
        @(posedge VPWR) disable iff (!VGND) (A1 == 1'b0) && (A2 == 1'b0) |-> (Y == 1'b0)
    );
    
    // Y is LOW when VPWR is HIGH, VGND is LOW, A1 is LOW, and A2 is HIGH.
    combinational_2: assert property (
        @(posedge VPWR) disable iff (!VGND) (VPWR == 1'b1) && (VGND == 1'b0) && (A1 == 1'b0) && (A2 == 1'b1) |-> (Y == 1'b0)
    );
    
    // Y is LOW when VPWR is LOW, VGND is HIGH, A1 is HIGH, and A2 is LOW.
    combinational_3: assert property (
        @(posedge VPWR) disable iff (!VGND) (VPWR == 1'b0) && (VGND == 1'b1) && (A1 == 1'b1) && (A2 == 1'b0) |-> (Y == 1'b0)
    );
    
    // Y is LOW when B1_N is HIGH.
    combinational_4: assert property (
        @(posedge VPWR) disable iff (!VGND) (B1_N == 1'b1) |-> (Y == 1'b0)
    );
    
    // Y is LOW when both VGND and VPB and VNB are HIGH.
    combinational_5: assert property (
        @(posedge VPWR) disable iff (!VGND) (VGND == 1'b1) && (VPB == 1'b1) && (VNB == 1'b1) |-> (Y == 1'b0)
    );
    
    // Y is HIGH otherwise.
    combinational_6: assert property (
        @(posedge VPWR) disable iff (!VGND) !(Y == 1'b0) |-> (Y == 1'b1)
    );
endmodule
```