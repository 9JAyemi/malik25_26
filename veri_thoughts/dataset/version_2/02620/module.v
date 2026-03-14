module complement (
    output [3:0] X,
    input  [3:0] A
);


    not inv1 (
       X[0],
       A[0]
    );

    not inv2 (
       X[1],
       A[1]
    );

    not inv3 (
       X[2],
       A[2]
    );

    not inv4 (
       X[3],
       A[3]
    );

endmodule