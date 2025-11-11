// SVA checker for my_module
module my_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic X
);

    // Functional equivalence (evaluate after updates with ##0 to avoid sampling races)
    assert property (@(A1 or A2 or B1 or C1 or X) ##0
                     (X === ((A1 & A2) || (B1 & C1))));

    // No spurious output changes without input changes
    assert property (@(A1 or A2 or B1 or C1 or X)
                     (!$changed({A1,A2,B1,C1})) |-> ##0 (!$changed(X)));

    // If inputs are all known, output must be known
    assert property (@(A1 or A2 or B1 or C1 or X)
                     (!$isunknown({A1,A2,B1,C1})) |-> ##0 (!$isunknown(X)));

    // Coverage: exercise each distinct cause and key edges
    cover property (@(A1 or A2 or B1 or C1 or X) ##0 ((A1 & A2) && !(B1 & C1) &&  X));
    cover property (@(A1 or A2 or B1 or C1 or X) ##0 ((B1 & C1) && !(A1 & A2) &&  X));
    cover property (@(A1 or A2 or B1 or C1 or X) ##0 ((A1 & A2) &&  (B1 & C1) &&  X));
    cover property (@(A1 or A2 or B1 or C1 or X) ##0 (!(A1 & A2) && !(B1 & C1) && !X));
    cover property (@(A1 or A2 or B1 or C1 or X) ##0 $rose(X));
    cover property (@(A1 or A2 or B1 or C1 or X) ##0 $fell(X));

endmodule

// Bind into DUT
bind my_module my_module_sva u_my_module_sva (.*);