// SVA checker for nand_gate_output
module nand_gate_output_sva (
    input  logic A_N, B_N, C, D,
    input  logic VPWR, VGND, VPB, VNB,
    input  logic Y,
    input  logic resetCounter,
    input  integer count
);

    function automatic bit known_inputs();
        return !$isunknown({A_N,B_N,C,D,VPWR,VGND,VPB,VNB});
    endfunction

    function automatic bit all_zero_known();
        return known_inputs() &&
               (A_N==1'b0 && B_N==1'b0 && C==1'b0 && D==1'b0 &&
                VPWR==1'b0 && VGND==1'b0 && VPB==1'b0 && VNB==1'b0);
    endfunction

    // Combinational correctness and X-dominance
    always @* begin
        if (!known_inputs()) begin
            assert ($isunknown(Y)) else
                $error("Y must be X when any input/supply is X");
            assert (resetCounter==1'b0) else
                $error("resetCounter must be 0 when any input/supply is X");
        end
        else begin
            assert (resetCounter == all_zero_known()) else
                $error("resetCounter must equal all_zero_known()");
            if (count >= 32 && count <= 39) begin
                assert (Y === 1'b0) else
                    $error("Y must be 0 when count in [32:39]");
            end
            else begin
                assert (Y === ~(A_N & B_N & C & D)) else
                    $error("NAND function mismatch");
            end
            assert (!$isunknown(Y)) else
                $error("Y unknown while all inputs/supplies known");
        end

        // Basic combinational coverage
        cover (!known_inputs() && $isunknown(Y));                    // X-prop observed
        cover (all_zero_known() && resetCounter);                    // resetCounter asserted
        cover (known_inputs() && (count>=32 && count<=39) && Y==0);  // forced-low window hit
        cover (known_inputs() && !(count>=32 && count<=39) &&
               (Y===~(A_N & B_N & C & D)));                          // normal NAND behavior
    end

    // Counter semantics (event-driven)
    // Reset dominates and sets count to 0 in the same timestep
    assert property (@(posedge resetCounter) ##0 (count==0));

    // If both edges happen, reset dominates
    assert property (@(posedge Y) resetCounter |-> ##0 (count==0));

    // On posedge Y without reset, count increments by exactly 1
    // $past(count,0) samples pre-update value in the same timestep
    assert property (@(posedge Y) !resetCounter |-> ##0 (count == $past(count,0)+1));

    // Coverage of entering/exiting forced-low window via Y pulses
    cover property (@(posedge Y) !resetCounter && known_inputs() && $past(count,0)==31 ##0 (count==32));
    cover property (@(posedge Y) !resetCounter && known_inputs() && $past(count,0)==39 ##0 (count==40));

endmodule

// Bind into DUT
bind nand_gate_output nand_gate_output_sva sva (
    .A_N(A_N), .B_N(B_N), .C(C), .D(D),
    .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
    .Y(Y), .resetCounter(resetCounter), .count(count)
);