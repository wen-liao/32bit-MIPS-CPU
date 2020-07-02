`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/10/2020 08:21:48 PM
// Design Name: 
// Module Name: cpu_32
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module cpu_32bit(A,B,ALUcont, result, zero);
    input wire[31:0] A, B;
    input wire[2:0] ALUcont;
    output wire[31:0] result;
    output wire zero;
    
    wire[31:0] minus;
    assign minus = A-B;
    assign result = (ALUcont === 3'b000) ? A&B :
        (ALUcont === 3'b001) ? A|B :
            (ALUcont === 3'b010) ? A+B :
                (ALUcont === 3'b100) ? A&~B :
                    (ALUcont === 3'b101) ? A|~B :
                        (ALUcont === 3'b110) ? minus :
                            (ALUcont === 3'b111) ? {31'b0, minus[31] } : 32'b0;
   assign zero = ~|result;
endmodule
