//
//  main.c
//  optimizer
//
//  Created by PUSHPENDU GHOSH on 28/10/16.
//  Copyright © 2016 PUSHPENDU. All rights reserved.
//

#include <stdio.h>
#include <math.h>

int maxormin , var , ineq , eq , noineq , novar;
int nosolution;
int balance=0,sourcesurplus=0,destsurplus=0;

typedef struct{
    double cost;
    int goods;
    int bvornot;//bv=1 while nonbv=0 nd -1 if not decided
    int zcoeff;
}transport;

typedef struct{
    int i;
    int j;
}position;

double mod(double x)
{
    if(x>=0)
        return x;
    else
        return -x;
}

void entries(double table[][novar+1]) //takes entries in simplex table
{
    int i,j;
    char op,junk;//operator <,>,=
    int calleq=0;


    for(i=0;i<=noineq;i++)//initializing all values to zero
    {
        for(j=0;j<novar+1;j++)
            table[i][j]=0;
    }

    printf("In objective fn enter coeffients of :\n");

    for(i=0;i<var;i++) //input of obj fn coeffients
    {
        printf("\tx%d : ",i+1);
        scanf("%lf",&table[0][i]);
        table[0][i]*=(-1);
    }

    printf("Constraints are : \n");
    for(i=0;i<ineq+eq;i++)
    {
        printf("%d : ",i+1);
        printf("Sign operator : ");
        scanf("%c %c",&junk,&op);

        for(j=0;j<var;j++)
        {
            printf("\tCoefficient of x%d = ",j+1);
            scanf("%lf",&table[i+1+calleq][j]);

            if(op==62)
                table[i+1+calleq][j]*=-1;
        }
        printf("\tOperates to = ");
        scanf("%lf",&table[i+1+calleq][novar]);

        if(op==62)
            table[i+1+calleq][novar]*=-1;

        if(op==60||op==62) //ascii of < is 60, > is 62
            table[i+1+calleq][var+i+calleq]=1;

        if(op==61)
        {
            table[i+1+calleq][var+i+calleq]=1;
            calleq++;
            for(j=0;j<var;j++)
            {
                table[i+1+calleq][j]=(table[i+calleq][j]*-1);
            }
            table[i+1+calleq][var+i+calleq]=1;
            table[i+1+calleq][novar]=(-1*table[i+calleq][novar]);
        }
    }
    printf("\n");
    for(i=0;i<=noineq;i++)
    {
        for(j=0;j<=novar;j++)
            printf(" %.2f ",table[i][j]);
        printf("\n");
    }
}

double determinant(double a[][noineq], double k)
{
    double s = 1, det = 0, b[noineq][noineq];
    int i, j, m, n, c;
    if (k == 1)
    {
        return (a[0][0]);
    }
    else
    {
        det = 0;
        for (c = 0; c < k; c++)
        {
            m = 0;
            n = 0;
            for (i = 0;i < k; i++)
            {
                for (j = 0 ;j < k; j++)
                {
                    b[i][j] = 0;
                    if (i != 0 && j != c)
                    {
                        b[m][n] = a[i][j];
                        if (n < (k - 2))
                            n++;
                        else
                        {
                            n = 0;
                            m++;
                        }
                    }
                }
            }
            det = det + s * (a[0][c] * determinant(b, k - 1));
            s = -1 * s;
        }
    }
    return (det);
}

void transpose(double num[noineq][noineq], double fac[noineq][noineq], double r, double inverse[][noineq])
{
    int i, j;
    double b[noineq][noineq], d;

    for (i = 0;i < r; i++)
    {
        for (j = 0;j < r; j++)
        {
            b[i][j] = fac[j][i];
        }
    }
    d = determinant(num, r);
    for (i = 0;i < r; i++)
    {
        for (j = 0;j < r; j++)
        {
            inverse[i][j] = b[i][j] / d;
        }
    }
}

void cofactor(double num[noineq][noineq], double f,double inverse[][noineq])
{
    double b[noineq][noineq], fac[noineq][noineq];
    int p, q, m, n, i, j;
    for (q = 0;q < f; q++)
    {
        for (p = 0;p < f; p++)
        {
            m = 0;
            n = 0;
            for (i = 0;i < f; i++)
            {
                for (j = 0;j < f; j++)
                {
                    if (i != q && j != p)
                    {
                        b[m][n] = num[i][j];
                        if (n < (f - 2))
                            n++;
                        else
                        {
                            n = 0;
                            m++;
                        }
                    }
                }
            }
            fac[q][p] = pow(-1, q + p) * determinant(b, f - 1);
        }
    }
    transpose(num, fac, f,inverse);
}

void inverse(double a[][noineq],double inverse[][noineq])
{
    double d;
    int k;
    k=noineq;
    d = determinant(a, k);
    cofactor(a, k,inverse);
}

void fillBs (double table[noineq+1][novar+1],int basicvar[noineq],double B[noineq][noineq],double Binverse[noineq][noineq],double Cb[noineq])
{
    int i,j;

    for(i=0;i<noineq;i++)
    {
        for(j=0;j<noineq;j++)
        {
            B[j][i]=table[j+1][basicvar[i]-1];
        }
    }
    for(i=0;i<noineq;i++)
        Cb[i]=-1*table[0][basicvar[i]-1];

    inverse(B,Binverse);
}

void gettable(double Cb[noineq],double Binverse[noineq][noineq],double table[noineq+1][novar+1],double newtable[noineq+1][novar+1],double Xb[noineq])
{
    int i,j,k;
    for(i=0;i<novar;i++)
    {
        for(j=0;j<noineq;j++)
        {
            newtable[j+1][i]=0;
            for(k=0;k<noineq;k++)
            {
                newtable[j+1][i]+=Binverse[j][k]*table[k+1][i];
            }
        }
    }
    for(i=0;i<novar;i++)
    {
        newtable[0][i]=table[0][i];
        for(j=0;j<noineq;j++)
            newtable[0][i]+=Cb[j]*newtable[j+1][i];
    }

    for(j=0;j<noineq;j++)
        newtable[j+1][novar]=Xb[j];

    newtable[0][novar]=0;
    for(j=0;j<noineq;j++)
        newtable[0][novar]+=Cb[j]*newtable[j+1][novar];
}

void iterator(double table[noineq+1][novar+1],int basicvar[noineq],double newtable[][novar+1])
{
    double B[noineq][noineq],Binverse[noineq][noineq],Xb[noineq],b[noineq],Cb[noineq];
    int i,j;

    for(i=0;i<noineq;i++)
        b[i]=table[i+1][novar];

    fillBs (table,basicvar,B,Binverse,Cb); //gives me B, inv(B) ,Cb

    printf("did the first iterator ");

    for(i=0;i<noineq;i++)
    {
        Xb[i]=0;
        for(j=0;j<noineq;j++)
        {
            Xb[i]=Xb[i]+(Binverse[i][j]*b[j]);
        }
    }

    gettable(Cb,Binverse,table,newtable,Xb);

}


void dualsimplex(double table[][novar+1],double newtable[][novar+1],int basicvar[noineq])
{
    int i; double min=0,ratio=-1;
    int lvindex,evindex;

    printf("hello");

    for(i=0;i<noineq;i++)
        basicvar[i]=i+var+1;

    printf("i am bfor iterator. ");

    iterator(table,basicvar,newtable);

    do{
        min=0;
        ratio=-1;
        for(i=0;i<noineq;i++)
        {
            if(newtable[i+1][novar]<min)//get the min from xb
            {
                min=newtable[i+1][novar];
                lvindex=i;
            }
        }
        if(min<0)//if there exist a negative entry
        {
            for(i=0;i<novar;i++)
            {
                if(newtable[lvindex+1][i]<0)//if a[i][j]<0
                {
                    if(ratio<0)
                    {
                        ratio=mod(newtable[0][i]/newtable[lvindex+1][i]);
                        evindex=i;
                    }

                    else if(ratio>mod(newtable[0][i]/newtable[lvindex+1][i]))
                    {
                        ratio=mod(newtable[0][i]/newtable[lvindex+1][i]);
                        evindex=i;
                    }
                }
            }
            if(ratio<0)
                nosolution=1; //this gives no solution
        }
        else
            return;

        if(basicvar[lvindex-1]==evindex+1)
            return;

        printf("x%d x%d\n",basicvar[lvindex-1],evindex+1);

        basicvar[lvindex]=evindex+1;
        iterator(table,basicvar,newtable);

        for(i=0;i<noineq;i++)
            printf("x%d ",basicvar[i]);
        printf("\n");


    }while(1);
}

void simplex(double table[][novar+1],double newtable[][novar+1],int basicvar[])
{
    double min=0,max=0;
    int evindex,lvindex;
    double ratio=-1;

    int i,j;

    if(maxormin==2)
    {
        do{
            max=0;
            ratio=-1;
            for(i=0;i<novar;i++)
            {
                if(newtable[0][i]>max)
                {
                    max=newtable[0][i];
                    evindex=i;
                }
            }
            if(max>0)
            {
                for(i=1;i<=noineq;i++)
                {
                    if(newtable[i][evindex]>0)
                    {
                        if(ratio<0)
                        {
                            ratio=(newtable[i][novar]/newtable[i][evindex]);
                            lvindex=i;
                        }

                        else if(ratio>(newtable[i][novar]/newtable[i][evindex]))
                        {
                            ratio=(newtable[i][novar]/newtable[i][evindex]);
                            lvindex=i;
                        }
                    }
                }
                if(ratio<0)
                    nosolution=1; //this gives no solution

            }
            else
                return;

            for(i=0;i<=noineq;i++)
            {
                for(j=0;j<=novar;j++)
                    printf(" %.2f ",newtable[i][j]);
                printf("\n");
            }printf("\n");

            if(basicvar[lvindex-1]==evindex+1)
                return;

            printf("x%d x%d\n",basicvar[lvindex-1],evindex+1);

            basicvar[lvindex-1]=evindex+1;
            iterator(table,basicvar,newtable);

            for(i=0;i<noineq;i++)
                printf("x%d ",basicvar[i]);
            printf("\n");

        }while(1);
    }
    if(maxormin==1)
    {
        do{ min=0;
            ratio=-1;
            for(i=0;i<novar;i++)
            {
                if(newtable[0][i]<min)
                {
                    min=newtable[0][i];
                    evindex=i;
                }
            }
            if(min<0)
            {
                for(i=1;i<=noineq;i++)
                {
                    if(newtable[i][evindex]>0)
                    {
                        if(ratio<0)
                        {
                            ratio=(newtable[i][novar]/newtable[i][evindex]);
                            lvindex=i;
                        }

                        else if(ratio>(newtable[i][novar]/newtable[i][evindex]))
                        {
                            ratio=(newtable[i][novar]/newtable[i][evindex]);
                            lvindex=i;
                        }
                    }
                }
                if(ratio<0)
                    nosolution=1; //this gives no solution
            }
            else
                return;

            for(i=0;i<=noineq;i++)
            {
                for(j=0;j<=novar;j++)
                    printf(" %.2f ",newtable[i][j]);
                printf("\n");
            }printf("\n");

            if(basicvar[lvindex-1]==evindex+1)
                return;

            printf("x%d x%d\n",basicvar[lvindex-1],evindex+1);

            basicvar[lvindex-1]=evindex+1;
            iterator(table,basicvar,newtable);
            for(i=0;i<noineq;i++)
                printf("x%d ",basicvar[i]);
            printf("\n");

        }while(1);
    }

}

void lppsolver()
{
    int i,j;

    printf("Maximize (enter 1) or minimize (enter 2) \nOption : ");
    scanf("%d",&maxormin);

    printf("\nEnter number of variable : ");
    scanf("%d",&var);

    printf("Enter number of inequations and equation as constraints resp. : ");
    scanf("%d %d",&ineq,&eq);

    noineq = ineq + 2*eq ;
    novar = var + 2*eq + ineq ;

    double table[noineq+1][novar+1];
    double newtable[noineq+1][novar+1];
    int basicvar[noineq];

    entries(table);

    printf("started dual\n");

    dualsimplex(table,newtable,basicvar);

    if(nosolution==1)
    {
        printf("This LPP has no solution.");
        printf("\n");
    }

    else
    {
        printf("\n");
        for(i=0;i<=noineq;i++)
        {
            for(j=0;j<=novar;j++)
                printf(" %.2f ",newtable[i][j]);
            printf("\n");
        }

        printf("Started simplex\n");

        simplex(table,newtable,basicvar);

        if(nosolution==1)
        {
            printf("This LPP has no solution.");
            printf("\n");
        }
        else
        {
            for(i=0;i<=noineq;i++)
            {
                for(j=0;j<=novar;j++)
                    printf(" %.2f ",newtable[i][j]);
                printf("\n");
            }
            for(i=0;i<noineq;i++)
                printf("x%d ",basicvar[i]);
            printf("are the basic variables after solving.");
        }
    }
}

void getbfs(int nosources,int nodest,transport table[][nodest+1],int source[], int destination[]) //nwcorner rule
{
    int i,j,k;

    for(i=0;i<nosources+1;i++)
    {
        for(j=0;j<nodest+1;j++)
        {
            if(table[i][j].bvornot!=0)
            {
                if(destination[j]<source[i])
                {

                    table[i][j].goods=destination[j];
                    table[i][j].bvornot=1;
                    source[i]-=destination[j];
                    destination[j]=0;

                    for(k=i+1;k<nosources+1;k++) //cut the col
                       table[k][j].bvornot=0;
                }

                else
                {
                    table[i][j].goods=source[i];
                    table[i][j].bvornot=1;
                    destination[j]-=source[i];
                    source[i]=0;

                    for(k=j+1;k<nodest+1;k++) //cut the row
                        table[i][k].bvornot=0;
                }
            }
        }
    }

    if(balance==1)
    {
        table[nosources][nodest].goods=0;
        table[nosources][nodest].bvornot=1;
    }

    for(i=0;i<nosources+1;i++)
    {
        for(j=0;j<nodest+1;j++)
        {
            if(table[i][j].bvornot==1)
                printf("%d ",table[i][j].goods);
            else if(table[i][j].bvornot==0)
                printf("NB ");
        }
        printf("\n");
    }

}

void top(int j, int nosources, int nodest,transport table[][nodest+1],int sourcegotvalue[],int destgotvalue[],int source[],int destination[]);

void left(int i, int nosources, int nodest,transport table[][nodest+1],int sourcegotvalue[],int destgotvalue[],int source[],int destination[])
{
    int j;
    int till;

    if(destsurplus==1)
        till=nodest;
    else
        till=nodest+1;

    for(j=0;j<till;j++)
    {
        if((table[i][j].bvornot==1)&&(destgotvalue[j]!=1))
           {
               destination[j]=table[i][j].cost-source[i];
               destgotvalue[j]=1;

               top(j,nosources,nodest,table,sourcegotvalue,destgotvalue,source,destination);
           }
    }
}
void top(int j, int nosources, int nodest,transport table[][nodest+1],int sourcegotvalue[],int destgotvalue[],int source[],int destination[])
{
    int i;
    int till;

    if(sourcesurplus==1)
        till=nosources;
    else
        till=nosources+1;

    for(i=0;i<till;i++)
    {
        if((table[i][j].bvornot==1)&&(sourcegotvalue[i]!=1))
        {
            source[i]=table[i][j].cost-destination[j];
            sourcegotvalue[i]=1;

            left(i,nosources,nodest,table,sourcegotvalue,destgotvalue,source,destination);
        }
    }
}

void getzrowofnonbv(int nosources, int nodest,transport table[][nodest+1],int source[],int destination[])
{
    int i,j;
    int itill,jtill;

    if(sourcesurplus==1)
        itill=nosources;
    else
        itill=nosources+1;

    if(destsurplus==1)
        jtill=nodest;
    else
        jtill=nodest+1;


    for(i=0;i<itill;i++)
    {
        for(j=0;j<jtill;j++)
        {
            if(table[i][j].bvornot==0)
            {
                table[i][j].zcoeff=source[i]+destination[j]-table[i][j].cost;
            }
        }
    }
}
int cpoint=0;
int endprocess=0;

void across(int nosources,int nodest, transport table[][nodest+1],position ev,position lv,position corner[]);
void down(int nosources,int nodest, transport table[][nodest+1],position ev,position lv,position corner[]);

void down(int nosources,int nodest, transport table[][nodest+1],position ev,position lv,position corner[])
{
    int i,j,iref;
    int itill;

    if(sourcesurplus==1)
        itill=nosources;
    else
        itill=nosources+1;

    if(cpoint==0)
        j=ev.j;

    else
        j=corner[cpoint].j;

    iref=corner[cpoint].i;

    for(i=0;i<itill;i++)
    {
        if(i!=iref)
        {
        if((table[i][j].bvornot==1)||(i==ev.i&&j==ev.j))
        {
            cpoint++;

            corner[cpoint].i=i;
            corner[cpoint].j=j;

            if(i==ev.i&&j==ev.j)
            {
                endprocess=1;
                return;
            }

            across(nosources,nodest,table,ev,lv,corner);

            if(endprocess==1)
                return;

            cpoint--;
        }
        }
    }
}
void across(int nosources,int nodest, transport table[][nodest+1],position ev,position lv,position corner[])
{
    int j,i,jref;
    int jtill;

    if(destsurplus==1)
        jtill=nodest;
    else
        jtill=nodest+1;

    i=corner[cpoint].i;
    jref=corner[cpoint].j;

    for(j=0;j<jtill;j++)
    {

        if(j!=jref){
        if(table[i][j].bvornot==1||(i==ev.i&&j==ev.j))
        {
            cpoint++;
            corner[cpoint].i=i;
            corner[cpoint].j=j;

            if(i==ev.i&&j==ev.j)
            {
                endprocess=1;
                return;
            }

            down(nosources,nodest,table,ev,lv,corner);

            if(endprocess==1)
                return;
            cpoint--;
        }
        }
    }
}

void looper(int nosources,int nodest,transport table[][nodest+1],position ev,position lv)
{
    int k;
    position corner[nosources+nodest+1];
    int theta=-1;

    //once initilialize the corner position
    for(k=0;k<nosources+nodest+1;k++)
    {
        corner[k].i=0;
        corner[k].j=0;
    }

    corner[0]=ev;

    down(nosources,nodest,table,ev,lv,corner); //didnt check across at the 1st check

    for(k=1;k<cpoint;k=k+2)
    {
        if((theta>table[corner[k].i][corner[k].j].goods)||theta<0||((theta==table[corner[k].i][corner[k].j].goods)&&(theta==table[corner[k].i][corner[k].j].cost>table[lv.i][lv.j].cost)))
        {
            theta=table[corner[k].i][corner[k].j].goods;
            lv.i=corner[k].i;
            lv.j=corner[k].j;
        }
    }

    for(k=1;k<cpoint;k=k+2)
    {
        table[corner[k].i][corner[k].j].goods-=theta;
    }
    for(k=2;k<cpoint;k=k+2)
    {
        table[corner[k].i][corner[k].j].goods+=theta;
    }

    //entering var
    table[ev.i][ev.j].goods=theta;
    table[ev.i][ev.j].bvornot=1;
    table[ev.i][ev.j].zcoeff=0;

    //leaving var
    table[lv.i][lv.j].goods=0;
    table[lv.i][lv.j].bvornot=0;
    table[lv.i][lv.j].zcoeff=0;

}

void solvetrans(int nosources,int nodest,transport table[][nodest+1],int source[],int destination[])
{

    int sourcegotvalue[nosources+1], destgotvalue[nodest+1];
    int i,j;
    int max=0;
    position ev,lv; ev.i=-1,ev.j=-1;

    source[0]=0;
    sourcegotvalue[0]=1;

    for(i=0;i<nosources+1;i++)
        sourcegotvalue[i]=0;

    for(i=0;i<nodest+1;i++)
        destgotvalue[i]=0;

    left(0,nosources,nodest,table,sourcegotvalue,destgotvalue,source,destination);

    getzrowofnonbv(nosources,nodest,table,source,destination);

    int itill,jtill;

    if(sourcesurplus==1)
        itill=nosources;
    else
        itill=nosources+1;

    if(destsurplus==1)
        jtill=nodest;
    else
        jtill=nodest+1;


    for(i=0;i<itill;i++)
    {
        for(j=0;j<jtill;j++)
        {
            if(table[i][j].bvornot==0)
            {
                if((table[i][j].zcoeff>max)||((max!=0)&&(table[i][j].zcoeff==max)&&(table[i][j].cost<table[ev.i][ev.j].cost)))
                {
                    max=table[i][j].zcoeff;
                    ev.i=i;
                    ev.j=j;
                }
            }

        }
    }

    if(max>0)
    {
        looper(nosources,nodest,table,ev,lv);
    }
    else
        return;

    cpoint=0;
    endprocess=0;

    solvetrans(nosources,nodest,table,source,destination);

    //iterator left

}
void manddest(int nosources,int nodest,transport table[][nodest+1])
{
    int j;
    char waste,opt;
    printf("\n\n(Enter 'y' if any of these destinations are mandatory) ->\n");

    for(j=0;j<nodest;j++)
    {
        printf("Destination %d : ",j+1);
        scanf("%c %c",&waste,&opt);

        if(opt=='y'||opt=='Y')
            table[nosources][j].cost=999999;
    }
}
void mandsupply(int nosources,int nodest,transport table[][nodest+1])
{
    int i;
    char waste,opt;
    printf("\n\n(Enter 'y' if any of these suppliers are mandatory) ->\n");

    for(i=0;i<nosources;i++)
    {
        printf(" Supply %d : ",i+1);
        scanf("%c %c",&waste,&opt);

        if(opt=='y'||opt=='Y')
            table[i][nodest].cost=999999;
    }
}

void transportation()
{
    int i,j;
    int nosources, nodest, totsource=0, totdest=0;
    double zcost=0;

    printf("Number of sources : ");
    scanf("%d",&nosources);

    printf("Number of destinations : ");
    scanf("%d",&nodest);

    int source[nosources+1],destination[nodest+1];
    transport table[nosources+1][nodest+1];

    for(i=0;i<nosources+1;i++)
    {
        for(j=0;j<nodest+1;j++)
        {
            table[i][j].cost=0;
            table[i][j].bvornot=-1;
        }
    }

    printf("\nSupply:\n");
    for(i=0;i<nosources;i++) //enter source supply capacity
    {
        printf("No. of units supplied by source%d : ",i+1);
        scanf("%d",&source[i]);
        totsource+=source[i];
    }

    printf("\nDestination:\n"); //entering destination requirement
    for(i=0;i<nodest;i++)
    {
        printf("No of units required by detination%d : ",i+1);
        scanf("%d",&destination[i]);
        totdest+=destination[i];
    }

    if(totdest>totsource)
    {
        printf("\n\nBeware!!creating dummy supplier : "); //choose an urgent supplier
        manddest(nosources,nodest,table);

        source[nosources]=totdest-totsource;
        destination[nodest]=0;
        destsurplus=1;
    }
    else if(totsource>totdest)
    {
        printf("\n\nBeware!!creating dummy destination : "); //choose an urgent destination
        mandsupply(nosources,nodest,table);

        destination[nodest]=-totdest+totsource;
        source[nosources]=0;
        sourcesurplus=1;
    }
    else //balanced model
    {
        printf("\n\nI got a balanced problem :-) ");
        source[nosources]=0;
        destination[nodest]=0;
        balance=1;
        destsurplus=1;
        sourcesurplus=1;
    }

    printf("\n\n");
    for(i=0;i<nosources;i++)
    {
        for(j=0;j<nodest;j++)
        {
            printf("Cost of trans ( S%d -> D%d) = ",i+1,j+1);
            scanf("%lf",&table[i][j].cost);
        }printf("\n");
    }

    getbfs(nosources,nodest,table,source,destination);
    solvetrans(nosources,nodest,table,source,destination);

    printf("\n\n");

    for(i=0;i<nosources+1;i++)
    {
        for(j=0;j<nodest+1;j++)
        {
            if(table[i][j].bvornot==1)
                printf("%d ",table[i][j].goods);
            else if(table[i][j].bvornot==0)
                printf("NB ");
        }
        printf("\n");
    }
    for(i=0;i<nosources+1;i++)
    {
        for(j=0;j<nodest+1;j++)
        {
            if(table[i][j].bvornot==1)
            {
                printf(" Source %d -> Destination %d : %d units at cost %.2f \n",i+1,j+1,table[i][j].goods,table[i][j].cost);
                zcost+=table[i][j].goods*table[i][j].cost;
            }
        }
    }
    printf("The minimum cost of trnsport is %.2f .",zcost);


}

void reducer(int workers, int jobs, float cost[][jobs])
{
    int i,j;
    float min;

    for(i=0;i<workers;i++)
    {
        for(j=0;j<jobs;j++)
        {
            printf("%.2f ",cost[i][j]);
        }
        printf("\n");
    }printf("\n");

    //Rowwise reduction
    for(i=0;i<workers;i++)
    {
        min=INFINITY;
        for(j=0;j<jobs;j++)
        {
            if(cost[i][j]<min)
                min=cost[i][j];
        }
        for(j=0;j<jobs;j++)
        {
            cost[i][j]-=min;
        }
    }

    for(i=0;i<workers;i++)
    {
        for(j=0;j<jobs;j++)
        {
            printf("%.2f ",cost[i][j]);
        }
        printf("\n");
    }printf("\n");

    //columnwise reduction
    for(j=0;j<jobs;j++)
    {
        min=INFINITY;
        for(i=0;i<workers;i++)
        {
            if(cost[i][j]<min)
                min=cost[i][j];
        }
        for(i=0;i<jobs;i++)
        {
            cost[i][j]-=min;
        }
    }

    for(i=0;i<workers;i++)
    {
        for(j=0;j<jobs;j++)
        {
            printf("%.2f ",cost[i][j]);
        }
        printf("\n");
    }printf("\n");

}

void horver(int workers, int jobs, int row, int col, int assigned[][jobs],int rowassigned[])
{
    int i,j;

    for(i=0;i<workers;i++)
        assigned[i][col]=0;

    for(j=0;j<jobs;j++)
        assigned[row][j]=0;

    assigned[row][col]=1;
    rowassigned[row]=1;

}

void randomzero(int workers,int jobs,float cost[][jobs],int assigned[][jobs],int rowassigned[],int randrows[],int randcol[])
{
    int i;
    printf("\n");
    for(i=0;i<workers;i++)
        printf(" %d ",rowassigned[i]);
}

void assigner(int workers, int jobs, float cost[][jobs],int assigned[][jobs])
{
    int i,j;
    int zeroes;
    int complete=0;
    int stopandgotorand=0;
    int alldone;
    int rowassigned[workers]; int randrows[workers], randcol[jobs];

    for(i=0;i<workers;i++)
        rowassigned[i]=0;

    do
    {
        for(i=0;i<workers;i++)
        {
            if(rowassigned[i]!=1)
            {
                zeroes=0;
                for(j=0;j<jobs;j++)
                {
                    if(cost[i][j]==0&&assigned[i][j]==2)
                        zeroes++;
                }
                if(zeroes==1)
                {
                    for(j=0;j<jobs;j++)
                    {
                        if(cost[i][j]==0)
                        {
                            horver(workers,jobs,i,j,assigned,rowassigned);
                            break;
                        }
                    }break;
                }
                if(zeroes==0)
                    stopandgotorand=1;
            }
        }
        alldone=0;
        for(i=0;i<workers;i++)
            alldone+=rowassigned[i];

        if(alldone==workers)
            complete=1;

    }while(complete==0&&stopandgotorand==0);

    if(stopandgotorand==1)
    {
        randomzero(workers,jobs,cost,assigned,rowassigned,randrows,randcol);
    }

}

void assignment()
{
    int jobs,workers;

    printf("\n\tASSIGNMENT PROBLEM\nNo. of jobs : ");
    scanf("%d",&jobs);

    workers=jobs;

    float cost[workers][jobs];
    float backcost[workers][jobs];
    int assigned[workers][jobs];

    int i,j;

    for(i=0;i<workers;i++)
    {
        for(j=0;j<jobs;j++)
        {
            assigned[i][j]=2;
        }
    }

    for(i=0;i<workers;i++)
    {
        printf("\n");
        for(j=0;j<jobs;j++)
        {
            printf("Cost if job%d is done by worker%d : ",j+1,i+1);
            scanf("%f",&cost[i][j]);
            backcost[i][j]=cost[i][j];
        }
    }
    printf("\n");

    reducer(workers,jobs,cost);

    assigner(workers,jobs,cost,assigned);

    float costassignment=0;

    for(i=0;i<workers;i++)
    {
        for(j=0;j<jobs;j++)
        {
            if(assigned[i][j]==1)
                costassignment+=backcost[i][j];
        }
    }
    printf("\nLeast cost to do all assignment = Rs.%f \n",costassignment);

}


int main()
{
    int option;

    printf("\t\tWelcome to optimizer :\n\n");
    printf("Select an option :\n\t1.Solve general a LPP.\n\t2.Transportation problem\n\t3.Assignment problem\nOption : ");
    scanf("%d",&option);

    switch(option)
    {
        case 1: lppsolver();
            break;

        case 2 : transportation();
            break;

        case 3: assignment();
            break;
    }


}
/* Mistakes :

    1. Only the non basic variable's ratio should be considered in dual --- completed correction
    2. Stoping unbounded solution ---- completed correction
 */

/* examples :

 maxormin=1;
 var=10;
 ineq=6;
 eq=3;

 noineq = ineq + 2*eq ;
 novar = var + 2*eq + ineq ;

 double table[noineq+1][novar+1];
 double newtable[noineq+1][novar+1];
 int basicvar[noineq];

 for(i=0;i<=noineq;i++)
 {
 for(j=0;j<novar+1;j++)
 table[i][j]=0;
 }

 table[0][0]=1000; table[0][3]=750; table[0][6]=250;
 table[0][1]=1000; table[0][4]=750; table[0][7]=250;
 table[0][2]=1000; table[0][5]=750; table[0][8]=250;

 table[1][0]=1;
 table[1][1]=1;
 table[1][2]=1; table[1][10]=1; table[1][22]=600;
 table[2][3]=1;
 table[2][4]=1;
 table[2][5]=1; table[2][11]=1; table[2][22]=500;
 table[3][6]=1;
 table[3][7]=1;
 table[3][8]=1; table[3][12]=1; table[3][22]=325;


 table[4][0]=1;  table[5][0]=-1;
 table[4][3]=1;  table[5][3]=-1;
 table[4][6]=1;  table[5][6]=-1;
 table[4][9]=-4;  table[5][9]=4;
 table[4][13]=1; table[5][14]=1;
 table[4][22]=0; table[5][22]=0;

 table[6][1]=1;  table[7][1]=-1;
 table[6][4]=1;  table[7][4]=-1;
 table[6][7]=1;  table[7][7]=-1;
 table[6][9]=-6;  table[7][9]=6;
 table[6][15]=1; table[7][16]=1;
 table[6][22]=0; table[7][22]=0;

 table[8][2]=1;  table[9][2]=-1;
 table[8][5]=1;  table[9][5]=-1;
 table[8][8]=1;  table[9][8]=-1;
 table[8][9]=-3;  table[9][9]=3;
 table[8][17]=1; table[9][18]=1;
 table[8][22]=0; table[9][22]=0;


 table[10][0]=3;
 table[10][3]=2;
 table[10][6]=1;  table[10][19]=1; table[10][22]=600;
 table[11][1]=3;
 table[11][4]=2;
 table[11][7]=1; table[11][20]=1; table[11][22]=800;
 table[12][2]=3;
 table[12][5]=2;
 table[12][8]=1; table[12][21]=1; table[12][22]=375;

 */
